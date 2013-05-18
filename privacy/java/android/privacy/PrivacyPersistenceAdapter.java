/**
 * Copyright (C) 2012 Svyatoslav Hresyk
 * This program is free software; you can redistribute it and/or modify it under
 * the terms of the GNU General Public License as published by the Free Software
 * Foundation; either version 3 of the License, or (at your option) any later version.
 * This program is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
 * PARTICULAR PURPOSE. See the GNU General Public License for more details.
 * You should have received a copy of the GNU General Public License along with
 * this program; if not, see <http://www.gnu.org/licenses>.
 */

package android.privacy;

import android.app.ActivityManagerNative;
import android.content.ContentValues;
import android.content.Context;
import android.content.Intent;
import android.content.pm.ApplicationInfo;
import android.content.pm.PackageManager;
import android.database.Cursor;
import android.database.SQLException;
import android.database.sqlite.SQLiteDatabase;
import android.database.sqlite.SQLiteException;
import android.os.FileUtils;
import android.os.RemoteException;
import android.os.Process;

import android.privacy.PrivacyWatchdog.PrivacyWatchdogInterface;
import android.privacy.utilities.PrivacyDebugger;
import android.util.Log;
import android.util.LruCache;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.security.InvalidParameterException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.locks.ReadWriteLock;
import java.util.concurrent.locks.ReentrantReadWriteLock;

/**
 * Responsible for persisting privacy settings to built-in memory
 * 
 * @author Svyatoslav Hresyk {@hide}
 */
public final class PrivacyPersistenceAdapter implements PrivacyWatchdogInterface {

    private static final String TAG = "PrivacyPersistenceAdapter";
    private static final int RETRY_QUERY_COUNT = 5;
    private static final String DATABASE_FILE = "/data/system/privacy.db";
    private static final String DATABASE_JOURNAL_FILE = "/data/system/privacy.db-journal";
    private static final int DATABASE_VERSION = 4;
    private static final boolean LOG_LOCKING = true;
    private static final boolean LOG_OPEN_AND_CLOSE = true;
    private static final boolean LOG_CACHE = true;
    public static final int DUMMY_UID = -1;

    /**
     * Thread safe object for determine how many threads currently have access to database
     */
    private final AtomicInteger sdbAccessThreads = new AtomicInteger();
    public static volatile int sDbVersion;

    /**
     * START DEBUG VARIABLES
     */
    private static volatile boolean useCache = true;
    private static volatile boolean autoCloseDb = false;
    /**
     * END DEBUG VARIABLES
     */
    // Used to lock the database during multi-statement operations to prevent
    // internally inconsistent data reads.
    // Multiple locks could be used to improve efficiency (i.e. for different tables)
    private static ReadWriteLock sDbLock = new ReentrantReadWriteLock();

    /**
     * Used to save settings for access from core libraries
     */
    public static final String SETTINGS_DIRECTORY = "/data/system/privacy";

    /**
     * Used for caching some settings
     */
    private PrivacyCache mCache = new PrivacyCache();

    /**
     * Since we're not able to extend from SQLiteDatabase we have to call the onauthorized methods on every write access to database!
     */
    private PrivacyWatchdog Watchdog;

    private static final String TABLE_SETTINGS = "settings";
    private static final String TABLE_MAP = "map";
    private static final String TABLE_ALLOWED_CONTACTS = "allowed_contacts";
    private static final String TABLE_VERSION = "version";

    private static final String RECEIVE_FAIL_SAFE_TRIGGERED = "android.privacy.RECEIVE_FAIL_SAFE_TRIGGERED";

    private static final String CREATE_TABLE_SETTINGS = 
        "CREATE TABLE IF NOT EXISTS " + TABLE_SETTINGS + " ( " + 
        " _id INTEGER PRIMARY KEY AUTOINCREMENT, " + 
        " packageName TEXT, " + 
        " uid INTEGER, " + 
        " deviceIdSetting INTEGER, " + 
        " deviceId TEXT, " + 
        " line1NumberSetting INTEGER, " + 
        " line1Number TEXT, " + 
        " locationGpsSetting INTEGER, " + 
        " locationGpsLat TEXT, " + 
        " locationGpsLon TEXT, " + 
        " locationNetworkSetting INTEGER, " + 
        " locationNetworkLat TEXT, " + 
        " locationNetworkLon TEXT, " + 
        " networkInfoSetting INTEGER, " + 
        " simInfoSetting INTEGER, " + 
        " simSerialNumberSetting INTEGER, " + 
        " simSerialNumber TEXT, " + 
        " subscriberIdSetting INTEGER, " + 
        " subscriberId TEXT, " + 
        " accountsSetting INTEGER, " + 
        " accountsAuthTokensSetting INTEGER, " + 
        " outgoingCallsSetting INTEGER, " + 
        " incomingCallsSetting INTEGER, " + 
        " contactsSetting INTEGER, " + 
        " calendarSetting INTEGER, " + 
        " mmsSetting INTEGER, " + 
        " smsSetting INTEGER, " + 
        " callLogSetting INTEGER, " + 
        " bookmarksSetting INTEGER, " + 
        " systemLogsSetting INTEGER, " + 
        " externalStorageSetting INTEGER, " + 
        " cameraSetting INTEGER, " + 
        " recordAudioSetting INTEGER, " + 
        " notificationSetting INTEGER, " + 
        " intentBootCompletedSetting INTEGER," + 
        " smsSendSetting INTEGER," + 
        " phoneCallSetting INTEGER," +
        " ipTableProtectSetting INTEGER," +
        " iccAccessSetting INTEGER," +
        " addOnManagementSetting INTEGER," + //this setting indicate if app is managed by addon or not
        " androidIdSetting INTEGER," +
        " androidId TEXT," +
        " wifiInfoSetting INTEGER," +
        " switchConnectivitySetting INTEGER," +
        " sendMmsSetting INTEGER," +
        " forceOnlineState INTEGER," + 
        " switchWifiStateSetting INTEGER" +
        ");";
    

    private static final String CREATE_TABLE_MAP = 
            "CREATE TABLE IF NOT EXISTS " + TABLE_MAP + "
                    ( name TEXT PRIMARY KEY, value TEXT );";
    
    private static final String CREATE_TABLE_ALLOWED_CONTACTS = 
            "CREATE TABLE IF NOT EXISTS " + TABLE_ALLOWED_CONTACTS 
            + " ( settings_id, contact_id, PRIMARY KEY(settings_id, contact_id) );";

    private static final String INSERT_VERSION = 
            "INSERT OR REPLACE INTO " + TABLE_MAP + " (name, value) "
            + "VALUES (\"db_version\", " + DATABASE_VERSION + ");";

    private static final String INSERT_ENABLED = 
            "INSERT OR REPLACE INTO " + TABLE_MAP + " (name, value) " 
            + "VALUES (\"enabled\", \"1\");";

    private static final String INSERT_NOTIFICATIONS_ENABLED = 
            "INSERT OR REPLACE INTO " + TABLE_MAP + " (name, value) " 
            + "VALUES (\"notifications_enabled\", \"1\");";

    private static final String[] DATABASE_FIELDS = new String[] { "_id", "packageName", "uid",
            "deviceIdSetting", "deviceId", "line1NumberSetting", "line1Number",
            "locationGpsSetting", "locationGpsLat", "locationGpsLon", "locationNetworkSetting",
            "locationNetworkLat", "locationNetworkLon", "networkInfoSetting", "simInfoSetting",
            "simSerialNumberSetting", "simSerialNumber", "subscriberIdSetting", "subscriberId",
            "accountsSetting", "accountsAuthTokensSetting", "outgoingCallsSetting",
            "incomingCallsSetting", "contactsSetting", "calendarSetting", "mmsSetting",
            "smsSetting", "callLogSetting", "bookmarksSetting", "systemLogsSetting",
            "externalStorageSetting", "cameraSetting", "recordAudioSetting", "notificationSetting",
            "intentBootCompletedSetting", "smsSendSetting", "phoneCallSetting",
            "ipTableProtectSetting", "iccAccessSetting", "addOnManagementSetting",
            "androidIdSetting", "androidId", "wifiInfoSetting", "switchConnectivitySetting",
            "sendMmsSetting", "forceOnlineState", "switchWifiStateSetting" };

    public static final String SETTING_ENABLED = "enabled";
    public static final String SETTING_NOTIFICATIONS_ENABLED = "notifications_enabled";
    public static final String SETTING_DB_VERSION = "db_version";
    public static final String VALUE_TRUE = "1";
    public static final String VALUE_FALSE = "0";

    private SQLiteDatabase mDb;

    private Context mContext;

    private boolean isFailSaveActive = false;

    public PrivacyPersistenceAdapter(Context context) {
        this.mContext = context;

        Watchdog = new PrivacyWatchdog(this);
        PrivacyDebugger.d(TAG, "Constructing " + TAG + " for package: " +  context.getPackageName()
                + "; Write permission for /data/system/: " + canWrite);
        // create the database and settings directory if we have write
        // permission and they do not exist
        if (new File("/data/system/").canWrite()) {
            if (!(new File(DATABASE_FILE).exists() && new File(SETTINGS_DIRECTORY).exists())) {
                if (LOG_LOCKING) PrivacyDebugger.d(TAG, 
                        "PrivacyPersistenceAdapter:constructor: WriteLock: (pre)lock");
                announceConnection();
                Watchdog.onBeginAuthorizedTransaction();
                sDbLock.writeLock().lock();
                if (LOG_LOCKING) PrivacyDebugger.d(TAG, 
                        "PrivacyPersistenceAdapter:constructor: WriteLock: (post)lock");
                try {
                    if (!new File(DATABASE_FILE).exists()) {
                        createDatabase();
                    }
                    if (!new File(SETTINGS_DIRECTORY).exists()) {
                        createSettingsDir();
                    }
                    sDbVersion = getDbVersion();
                    PrivacyDebugger.d(TAG, "PrivacyPersistenceAdapter - current DB version: " + currentVersion);
                    if (sDbVersion < DATABASE_VERSION) {
                        upgradeDatabase();
                    }
                    fillPrivacyCache();
                } catch(Exception e) {
                    PrivacyDebugger.e(TAG, "got exception while trying to create database and/or"
                            + "settingsDirectories");
                } finally {
                    if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                            "PrivacyPersistenceAdapter:constructor: WriteLock: (pre)unlock");
                    sDbLock.writeLock().unlock();
                    if (LOG_LOCKING) PrivacyDebugger.d(TAG, 
                            "PrivacyPersistenceAdapter:constructor: WriteLock: (post)unlock");
                    Watchdog.onEndAuthorizedTransaction();
                    closeIdleDatabase();
                }
            }
        }
    }


    private void upgradeDatabase() {
        if (sDbVersion < DATABASE_VERSION) {
            PrivacyDebugger.i(TAG, "upgradeDatabase - upgrading DB from version " + currentVersion + " to " + DATABASE_VERSION);

        announceConnection();
        sDbLock.writeLock().lock();
        Watchdog.onBeginAuthorizedTransaction();
        SQLiteDatabase db = null;

        try {
            db = getDatabase();
            db.beginTransaction();
            switch (currentVersion) {
                case 1:
                case 2:
                case 3:
                    if (db != null && db.isOpen()) {
                        db.execSQL("DROP TABLE IF EXISTS " + TABLE_VERSION + ";");
                        db.execSQL(CREATE_TABLE_ALLOWED_CONTACTS);
                        db.execSQL(CREATE_TABLE_MAP);
                        db.execSQL(INSERT_VERSION);
                        db.execSQL(INSERT_ENABLED);
                        db.execSQL(INSERT_NOTIFICATIONS_ENABLED);

                        // remove uid dirs from the settings directory
                        File settingsDir = new File(SETTINGS_DIRECTORY);
                        for (File packageDir : settingsDir.listFiles()) {
                            for (File uidDir : packageDir.listFiles()) {
                                if (uidDir.isDirectory()) {
                                    File[] settingsFiles = uidDir.listFiles();
                                    // copy the first found (most likely the only one) one level up
                                    if (settingsFiles[0] != null) {
                                        File newPath = new File(packageDir + "/" + settingsFiles[0].getName());
                                        newPath.delete();
                                        settingsFiles[0].renameTo(newPath);
                                        deleteRecursive(uidDir);
                                    }
                                }
                            }
                        }

                        db.setTransactionSuccessful();
                    } else {
                        PrivacyDebugger.e(TAG, "cannot upgrade database because database is null or isn't open!");
                    }
                    break;

                case 4:
                    if (db != null && db.isOpen()) {
                        db.execSQL("DROP TABLE IF EXISTS " + TABLE_VERSION + ";");
                        db.execSQL("DROP TABLE IF EXISTS " + TABLE_SETTINGS + ";");
                        db.execSQL(CREATE_TABLE_SETTINGS);
                        db.execSQL(INSERT_VERSION);

                        removeFiles(SETTINGS_DIRECTORY);
                        db.setTransactionSuccessful();
                    } else {
                        PrivacyDebugger.e(TAG, "cannot upgrade database because database is null or isn't open!");
                    }
                    break;
            }
            purgeSettings();
        } catch(Exception e) {
            PrivacyDebugger.w(TAG, "upgradeDatabase - could not upgrade DB", e);
        } finally {
            watchDog.onEndAuthorizedTransaction();
            sDbLock.writeLock().lock();
            closeIdleDatabase();

        }
    }

    private int getDbVersion() {
        String versionString = getValue(SETTING_DB_VERSION);
        if (versionString == null) {
            PrivacyDebugger.e(TAG, "PrivacyPersistenceAdapter:getDbVersion: "
                    + "getValue returned null; assuming version = 1");
            return 1;
        } else {
            try {
                return Integer.parseInt(versionString);
            } catch (Exception e) {
                PrivacyDebugger.e(TAG, "PrivacyPersistenceAdapter:getDbVersion: "
                        + "failed to parse database version; returning 1");
                return 1;
            }
        }
    }

    
    public String getValue(String name) {
        SQLiteDatabase db;
        Cursor c;
        String output = null;

        try {
            announceConnection();
            if (LOG_OPEN_AND_CLOSE) PrivacyDebugger.d(TAG, 
                    + "PrivacyPersistenceAdapter:getValue: "
                    + "Increment DB access threads: now " 
                    + Integer.toString(sDbAccessThreads));
            db = getDatabase();
            if (db == null || !db.isOpen()) {
                PrivacyDebugger.e(TAG, "PrivacyPersistenceAdapter:getValue: "
                        + "Database not obtained while getting value for name: " + name);
                return null;
            }

            if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                    "PrivacyPersistenceAdapter:getValue: ReadLock: (pre)lock");
            sDbLock.readLock().lock();
            if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                    "PrivacyPersistenceAdapter:getValue: ReadLock: (post)lock");
            try {

                c = query(db, TABLE_MAP, new String[] { "value" }, "name=?", new String[] { name },
                        null, null, null, null);
                if (c != null && c.getCount() > 0 && c.moveToFirst()) {
                    output = c.getString(c.getColumnIndex("value"));
                    c.close();
                } else {
                    PrivacyDebugger.w(TAG, "PrivacyPersistenceAdapter:getValue: "
                            + "Could not get value for name: "+ name);
                }
            } catch (Exception e) {
                PrivacyDebugger.e(TAG, "PrivacyPersistenceAdapter:getValue: "
                        + "Exception occurred while getting value for name: " + name, e);
            } finally {
                if (LOG_LOCKING) PrivacyDebugger.d(TAG, 
                        "PrivacyPersistenceAdapter:getValue: ReadLock: (pre)unlock");
                sDbLock.readLock().unlock();
                if (LOG_LOCKING) PrivacyDebugger.d(TAG, 
                        "PrivacyPersistenceAdapter:getValue: ReadLock: (post)unlock");
            }

        } finally {
            closeIdleDatabase();
        }
        return output;
    }
    
    public boolean setValue(String name, String value) {
        PrivacyDebugger.e(TAG, "setValue - name " + name + " value " + value);
        ContentValues values = new ContentValues();
        values.put("name", name);
        values.put("value", value);

        boolean success = false;

        SQLiteDatabase db;

        try {
            announceConnection();
            Watchdog.onBeginAuthorizedTransaction();
            if (LOG_OPEN_AND_CLOSE) PrivacyDebugger.d(TAG, 
                    "PrivacyPersistenceAdapter:setValue: Increment DB access threads: now "
                    + Integer.toString(sDbAccessThreads));
            db = getDatabase();
            if (db == null || !db.isOpen()) {
                PrivacyDebugger.e(TAG, "PrivacyPersistenceAdapter:setValue: "
                        + "Database not obtained while setting value for name: " + name);
                return false;
            }
            
            // updating the version is atomic, but we need to use a lock
            // to make sure we don't try to get/update the version while the DB is being 
            // created or upgraded
            if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                    "PrivacyPersistenceAdapter:setValue: WriteLock: (pre)lock");
            sDbLock.writeLock().lock();
            if (LOG_LOCKING) PrivacyDebugger.d(TAG, 
                    "PrivacyPersistenceAdapter:setValue: WriteLock: (post)lock");
            try {
                success = db.replace(TABLE_MAP, null, values) != -1;
            } finally {
                if (LOG_LOCKING) PrivacyDebugger.d(TAG, 
                        "PrivacyPersistenceAdapter:setValue: WriteLock: (pre)unlock");
                sDbLock.writeLock().unlock();
                if (LOG_LOCKING) PrivacyDebugger.d(TAG, 
                        "PrivacyPersistenceAdapter:setValue: WriteLock: (post)unlock");
            }
        } finally {
            Watchdog.onEndAuthorizedTransaction();
            closeIdleDatabase();
        }

        return success;
    }

    public PrivacySettings getSettings(String packageName) {
        return getSettings(packageName, false);
    }

    /**
     * Retrieve privacy settings for a single package
     * 
     * @param packageName
     *            package for which to retrieve settings
     * @return privacy settings for the package, or null if no settings exist
     *         for it
     */
    public PrivacySettings getSettings(String packageName) {
        PrivacySettings privacySettings = null;

        if (packageName == null) {
            throw new InvalidParameterException(
                    "PrivacyPersistenceAdapter:getSettings:insufficient application "
                            + "identifier - package name is required");
        }
        if(isFailSafeActive() && !fillCache) { 
            PrivacyDebugger.w(TAG,"failSafeMode is active -> return blocked privacy object!");
            return PrivacySettings.getFailSaveObject();
        }
        
        if(mCache.containsSetting(packageName)) {
            return mCache.getSettings(packageName);
        }

        announceConnection();
        sDbLock.readLock().lock();

        SQLiteDatabase db;
        try {
            // indicate that the DB is being read to prevent closing by other threads
            synchronized (sDbAccessThreads) {
                sDbAccessThreads++;
            }
            if (LOG_OPEN_AND_CLOSE) PrivacyDebugger.d(TAG, 
                    "PrivacyPersistenceAdapter:getSettings: "
                    + "Increment DB access threads: now " 
                    + Integer.toString(sDbAccessThreads));
            db = getDatabase();
        } catch (SQLiteException e) {
            PrivacyDebugger.e(TAG, "getSettings - database could not be opened", e);
            closeIdleDatabase();
            throw e;
        }

        Cursor cursor = null;

        if (LOG_LOCKING) PrivacyDebugger.d(TAG, 
                "PrivacyPersistenceAdapter:getSettings: ReadLock: (pre)lock");
        sDbLock.readLock().lock();
        if (LOG_LOCKING) PrivacyDebugger.d(TAG, 
                "PrivacyPersistenceAdapter:getSettings: ReadLock: (post)lock");
        try {
            cursor = query(db, TABLE_SETTINGS, DATABASE_FIELDS, "packageName=?",
                    new String[] { packageName }, null, null, null, null);

            if (cursor != null) {
                if (cursor.getCount() == 0) {
                    // No settings are present: log that and do nothing
                    PrivacyDebugger.d(TAG, 
                            "PrivacyPersistenceAdapter:getSettingsfound for package " 
                            + packageName);
                } else {
                    if (cursor.getCount() > 1) {
                        PrivacyDebugger.w(TAG, 
                                "Multiple privacy settings found for package "
                                + packageName);
                    }
    
                    if (cursor.moveToFirst()) {
                        privacySettings = new PrivacySettings(cursor.getInt(0),
                                cursor.getString(1), cursor.getInt(2), 
                                (byte) cursor.getShort(3), cursor.getString(4),
                                (byte) cursor.getShort(5), cursor.getString(6),
                                (byte) cursor.getShort(7), cursor.getString(8),
                                cursor.getString(9), (byte) cursor.getShort(10), 
                                cursor.getString(11), cursor.getString(12),
                                (byte) cursor.getShort(13), (byte) cursor.getShort(14),
                                (byte) cursor.getShort(15), cursor.getString(16),
                                (byte) cursor.getShort(17), cursor.getString(18),
                                (byte) cursor.getShort(19), (byte) cursor.getShort(20),
                                (byte) cursor.getShort(21), (byte) cursor.getShort(22),
                                (byte) cursor.getShort(23), (byte) cursor.getShort(24),
                                (byte) cursor.getShort(25), (byte) cursor.getShort(26),
                                (byte) cursor.getShort(27), (byte) cursor.getShort(28),
                                (byte) cursor.getShort(29), (byte) cursor.getShort(30),
                                (byte) cursor.getShort(31), (byte) cursor.getShort(32),
                                (byte) cursor.getShort(33), (byte) cursor.getShort(34), null,
                                (byte) cursor.getShort(35), (byte) cursor.getShort(36),
                                (byte) cursor.getShort(37), (byte) cursor.getShort(38),
                                (byte) cursor.getShort(39), (byte) cursor.getShort(40),
                                cursor.getString(41), (byte) cursor.getShort(42),
                                (byte) cursor.getShort(43), (byte) cursor.getShort(44),
                                (byte) cursor.getShort(45), (byte) cursor.getShort(46));
    
                        // get allowed contacts IDs if necessary
                        cursor = query(db, TABLE_ALLOWED_CONTACTS, 
                                new String[] { "contact_id" },
                                "settings_id=?",
                                new String[] { Integer.toString(privacySettings.get_id()) },
                                null,null, null, null);
                        if (cursor != null && cursor.getCount() > 0) {
                            int[] allowedContacts = new int[cursor.getCount()];
                            while (cursor.moveToNext())
                                allowedContacts[cursor.getPosition()] = cursor.getInt(0);
                            privacySettings.setAllowedContacts(allowedContacts);
                            PrivacyDebugger.d(TAG, "getSettings - found settings entry for package: " + packageName);
                            mCache.updateOrSaveSettings(s); 
                        } else {
                           PrivacyDebugger.e(TAG, "getSettings - no settings found for package: " + packageName);
                        }
                    }
                }
            }
        } catch (Exception e) {
            PrivacyDebugger.e(TAG, "getSettings - failed to get settings for package: " 
                    + packageName, e);
        } finally {
            if (cursor != null)
                cursor.close();
            if (LOG_LOCKING) PrivacyDebugger.d(TAG, 
                        "PrivacyPersistenceAdapter:getSettings: ReadLock: (pre)unlock");
            sDbLock.readLock().unlock();
            if (LOG_LOCKING) PrivacyDebugger.d(TAG, 
                    "PrivacyPersistenceAdapter:getSettings: ReadLock: (post)unlock");
            closeIdleDatabase();
        }
        
        return privacySettings;
    }

    /**
     * Saves the settings object fields into DB and into plain text files where
     * applicable. The DB changes will not be made persistent if saving settings
     * to plain text files fails.
     * 
     * @param s
     *            settings object
     * @return true if settings were saved successfully, false otherwise
     */
    public boolean saveSettings(PrivacySettings s) {
        boolean result = false;

        String packageName = s.getPackageName();

        if (packageName == null || packageName.isEmpty()) {
            PrivacyDebugger.e(TAG, "saveSettings - either package name is missing");
            return false;
        }

        ContentValues values = new ContentValues();
        values.put("packageName", packageName);
        // values.put("uid", uid);
        values.put("uid", DUMMY_UID);

        values.put("deviceIdSetting", s.getDeviceIdSetting());
        values.put("deviceId", s.getDeviceId());

        values.put("line1NumberSetting", s.getLine1NumberSetting());
        values.put("line1Number", s.getLine1Number());

        values.put("locationGpsSetting", s.getLocationGpsSetting());
        values.put("locationGpsLat", s.getLocationGpsLat());
        values.put("locationGpsLon", s.getLocationGpsLon());

        values.put("locationNetworkSetting", s.getLocationNetworkSetting());
        values.put("locationNetworkLat", s.getLocationNetworkLat());
        values.put("locationNetworkLon", s.getLocationNetworkLon());

        values.put("networkInfoSetting", s.getNetworkInfoSetting());
        values.put("simInfoSetting", s.getSimInfoSetting());

        values.put("simSerialNumberSetting", s.getSimSerialNumberSetting());
        values.put("simSerialNumber", s.getSimSerialNumber());
        values.put("subscriberIdSetting", s.getSubscriberIdSetting());
        values.put("subscriberId", s.getSubscriberId());

        values.put("accountsSetting", s.getAccountsSetting());
        values.put("accountsAuthTokensSetting", s.getAccountsAuthTokensSetting());
        values.put("outgoingCallsSetting", s.getOutgoingCallsSetting());
        values.put("incomingCallsSetting", s.getIncomingCallsSetting());

        values.put("contactsSetting", s.getContactsSetting());
        values.put("calendarSetting", s.getCalendarSetting());
        values.put("mmsSetting", s.getMmsSetting());
        values.put("smsSetting", s.getSmsSetting());
        values.put("callLogSetting", s.getCallLogSetting());
        values.put("bookmarksSetting", s.getBookmarksSetting());
        values.put("systemLogsSetting", s.getSystemLogsSetting());
        values.put("notificationSetting", s.getNotificationSetting());
        values.put("intentBootCompletedSetting", s.getIntentBootCompletedSetting());
        // values.put("externalStorageSetting", s.getExternalStorageSetting());
        values.put("cameraSetting", s.getCameraSetting());
        values.put("recordAudioSetting", s.getRecordAudioSetting());
        values.put("smsSendSetting", s.getSmsSendSetting());
        values.put("phoneCallSetting", s.getPhoneCallSetting());
        values.put("ipTableProtectSetting", s.getIpTableProtectSetting());
        values.put("iccAccessSetting", s.getIccAccessSetting());
        values.put("addOnManagementSetting", s.getAddOnManagementSetting());
        values.put("androidIdSetting", s.getAndroidIdSetting());
        values.put("androidId", s.getAndroidID());
        values.put("wifiInfoSetting", s.getWifiInfoSetting());
        values.put("switchConnectivitySetting", s.getSwitchConnectivitySetting());
        values.put("sendMmsSetting", s.getSendMmsSetting());
        values.put("forceOnlineState", s.getForceOnlineState());
        values.put("switchWifiStateSetting", s.getSwitchWifiStateSetting());

        announceConnection();
        sDbLock.writeLock().lock();
        Watchdog.onBeginAuthorizedTransaction();
        SQLiteDatabase db = null;
        Cursor cursor = null;

        try {
            synchronized (sDbAccessThreads) {
                sDbAccessThreads++;
            }
            if (LOG_OPEN_AND_CLOSE) PrivacyDebugger.d(TAG, 
                    "PrivacyPersistenceAdapter:saveSettings: "
                    + "Increment DB access threads: now " 
                    + Integer.toString(sDbAccessThreads));
            db = getDatabase();

            if (db != null && db.isOpen()) {
                if (LOG_LOCKING) PrivacyDebugger.d(TAG, 
                        "PrivacyPersistenceAdapter:saveSettings: WriteLock: "
                        + "(pre)lock");
                sDbLock.writeLock().lock();
                if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                        "PrivacyPersistenceAdapter:saveSettings: WriteLock: "
                        + "(post)lock");
                try {
                    if (LOG_LOCKING) PrivacyDebugger.d(TAG, 
                            "PrivacyPersistenceAdapter:saveSettings: "
                            + "Transaction: (pre)begin");
                    db.beginTransaction();
                    if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                            "PrivacyPersistenceAdapter:saveSettings: "
                            + "Transaction: (post)begin");
                    try {

                        // save settings to the DB
                        Integer id = s.get_id();

                        if (id != null) { // existing entry -> update
                            if (db.update(TABLE_SETTINGS, values, "_id=?", 
                                    new String[] { id.toString() }) < 1) {
                                throw new Exception("saveSettings - "
                                        + "failed to update database entry");
                            }

                            db.delete(TABLE_ALLOWED_CONTACTS, "settings_id=?", 
                                    new String[] { id.toString() });
                            int[] allowedContacts = s.getAllowedContacts();
                            if (allowedContacts != null) {
                                ContentValues contactsValues = new ContentValues();
                                for (int i = 0; i < allowedContacts.length; i++) {
                                    contactsValues.put("settings_id", id);
                                    contactsValues.put("contact_id", allowedContacts[i]);
                                    if (db.insert(TABLE_ALLOWED_CONTACTS, null, 
                                            contactsValues) == -1)
                                        throw new Exception(
                                                "PrivacyPersistenceAdapter:saveSettings: "
                                                + "failed to update database entry (contacts)");
                                }
                            }

                        } else { // new entry -> insert if no duplicates exist
                            // PrivacyDebugger.d(TAG,
                            // "saveSettings - new entry; verifying if duplicates exist");
                            cursor = db.query(TABLE_SETTINGS, 
                                    new String[] { "_id" }, "packageName=?",
                                    new String[] { s.getPackageName() }, null, null, null);
                            if (cursor != null) {
                                if (cursor.getCount() == 1) { 
                                    // exactly one entry exists -> update
                                    // PrivacyDebugger.d(TAG,
                                    //         "saveSettings - updating existing entry");
                                    if (db.update(TABLE_SETTINGS, values, "packageName=?",
                                            new String[] { s.getPackageName() }) < 1) {
                                        throw new Exception("saveSettings - "
                                                + "failed to update database entry");
                                    }

                                    if (cursor.moveToFirst()) {
                                        Integer idAlt = cursor.getInt(0); // id of the found
                                        // duplicate entry
                                        db.delete(TABLE_ALLOWED_CONTACTS, "settings_id=?",
                                                new String[] { idAlt.toString() });
                                        int[] allowedContacts = s.getAllowedContacts();
                                        if (allowedContacts != null) {
                                            ContentValues contactsValues = new ContentValues();
                                            for (int i = 0; i < allowedContacts.length; i++) {
                                                contactsValues.put("settings_id", idAlt);
                                                contactsValues.put("contact_id", allowedContacts[i]);
                                                if (db.insert(TABLE_ALLOWED_CONTACTS, null, 
                                                        contactsValues) == -1)
                                                    throw new Exception(
                                                            "saveSettings - failed to update "
                                                            + "database entry (contacts)");
                                            }
                                        }
                                    }
                                } else if (cursor.getCount() == 0) { // no entries -> insert
                                    // Privacydebugger.d(TAG, 
                                    //         "saveSettings - inserting new entry");
                                    long rowId = db.insert(TABLE_SETTINGS, null, values);
                                    if (rowId == -1) {
                                        throw new Exception(
                                                "PrivacyPersistenceAdapter:saveSettings - "
                                                + "failed to insert new record into DB");
                                    }

                                    db.delete(TABLE_ALLOWED_CONTACTS, "settings_id=?",
                                            new String[] { Long.toString(rowId) });
                                    int[] allowedContacts = s.getAllowedContacts();
                                    if (allowedContacts != null) {
                                        ContentValues contactsValues = new ContentValues();
                                        for (int i = 0; i < allowedContacts.length; i++) {
                                            contactsValues.put("settings_id", rowId);
                                            contactsValues.put("contact_id", allowedContacts[i]);
                                            if (db.insert(TABLE_ALLOWED_CONTACTS, null, 
                                                    contactsValues) == -1)
                                                throw new Exception(
                                                        "PrivacyPersistenceAdapter:saveSettings:"
                                                        + "failed to update database entry "
                                                        + "(contacts)");
                                        }
                                    }
                                } else {
                                    // something went totally wrong and there are
                                    // multiple entries for same identifier
                                    throw new Exception("PrivacyPersistenceAdapter:saveSettings:"
                                            + "duplicate entries in the privacy.db");
                                }
                            } else {
                                // jump to catch block to avoid marking transaction as
                                // successful
                                throw new Exception("PrivacyPersistenceAdapter:saveSettings:"
                                        + "cursor is null, database access failed");
                            }
                        }

                        // save settings to plain text file (for access from core libraries)
                        if (!writeExternalSettings("systemLogsSetting", packageName, s)) {
                            throw new Exception("PrivacyPersistenceAdapter:saveSettings:"
                                    + "failed to write systemLogsSettings file");
                        }
                        if (!writeExternalSettings("ipTableProtectSetting", packageName, s)) {
                            throw new Exception("PrivacyPersistenceAdapter:saveSettings:"
                                    + "failed to write ipTableProtectSetting file");
                        }

                        // mark DB transaction successful (commit the changes)
                        db.setTransactionSuccessful();
                        mCache.updateOrSaveSettings(s);
                        PrivacyDebugger.d(TAG, "saveSettings - completing transaction");
                    } finally {
                        if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                                "PrivacyPersistenceAdapter:saveSettings: "
                                + "Transaction: (pre)end");
                        // we want to transition from set transaction successful to end 
                        // as fast as possible to avoid errors (see the Android docs)
                        db.endTransaction(); 
                        if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                                "PrivacyPersistenceAdapter:saveSettings: "
                                + "Transaction: (post)end");
                        
                        if (cursor != null) {
                            cursor.close();
                        }
                    }
                } finally {
                    if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                            "PrivacyPersistenceAdapter:saveSettings: "
                            + "WriteLock: (pre)unlock");
                    sDbLock.writeLock().unlock();
                    if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                            "PrivacyPersistenceAdapter:saveSettings: "
                            + "WriteLock: (post)unlock");
                }
                result = true;
            }
        } catch (Exception e) {
            PrivacyDebugger.e(TAG, "PrivacyPersistenceAdapter:saveSettings: saving for "
                    + packageName + " failed", e);
        } finally {
            Watchdog.onEndAuthorizedTransaction();
            closeIdleDatabase();
        }

        return result;
    }

    /**
     * This method creates external settings files for access from core libraries
     * 
     * @param settingsName
     *            field name from database
     * @param packageName
     *            name of package
     * @param s
     *            settings from package
     * @return true if file was successful written
     * @throws Exception
     *             if we cannot write settings to directory
     */
    private boolean writeExternalSettings(String settingsName, String packageName, 
            PrivacySettings s) throws Exception {
        // save settings to plain text file (for access from core libraries)
        File settingsPackageDir = new File("/data/system/privacy/" + packageName + "/");
        File systemLogsSettingFile = new File("/data/system/privacy/" + packageName + "/" + "/"
                + settingsName);
        boolean result = false;
        
        if (LOG_LOCKING) PrivacyDebugger.d(TAG, 
                "PrivacyPersistenceAdapter:writeExternalSettings: "
                + "WriteLock: (pre)lock");
        sDbLock.writeLock().lock();
        if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                "PrivacyPersistenceAdapter:writeExternalSettings: "
                + "WriteLock: (post)lock");
        try {
            settingsPackageDir.mkdirs();
            settingsPackageDir.setReadable(true, false);
            settingsPackageDir.setExecutable(true, false);
            // create the setting files and make them readable
            systemLogsSettingFile.createNewFile();
            systemLogsSettingFile.setReadable(true, false);
            // write settings to files
            // PrivacyDebugger.d(TAG, "saveSettings - writing to file");
            OutputStreamWriter writer = new OutputStreamWriter(new FileOutputStream(
                    systemLogsSettingFile));
            // now decide which feature of setting we have to save
            if (settingsName.equals("systemLogsSetting"))
                writer.append(s.getSystemLogsSetting() + "");
            else if (settingsName.equals("ipTableProtectSetting"))
                writer.append(s.getIpTableProtectSetting() + "");
            writer.flush();
            writer.close();
            result = true;
        } catch (IOException e) {
            // jump to catch block to avoid marking transaction as successful
            throw new Exception("saveSettings - could not write settings to file", e);
        } finally {
            if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                    "PrivacyPersistenceAdapter:writeExternalSettings: "
                    + "WriteLock: (pre)unlock");
            sDbLock.writeLock().unlock();
            if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                    "PrivacyPersistenceAdapter:writeExternalSettings: "
                    + "WriteLock: (post)unlock");
        }
        
        return true;
    }

    /**
     * Deletes a settings entry from the DB
     * 
     * @return true if settings were deleted successfully, false otherwise
     */
    public boolean deleteSettings(String packageName) {
        boolean result = true;
        announceConnection();
        Watchdog.onBeginAuthorizedTransaction();
        SQLiteDatabase db = null;
 
       try {
            if (LOG_OPEN_AND_CLOSE) PrivacyDebugger.d(TAG,
                    "PrivacyPersistenceAdapter:deleteSettings: "
                    + "Increment DB access threads: now " + Integer.toString(sDbAccessThreads));
            db = getDatabase();

            if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                    "PrivacyPersistenceAdapter:deleteSettings: "
                    + "WriteLock: (pre)lock");
            sDbLock.writeLock().lock();
            if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                    "PrivacyPersistenceAdapter:deleteSettings: "
                    + "WriteLock: (post)lock");
            try {
                if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                        "PrivacyPersistenceAdapter:deleteSettings: "
                        + "Transaction: (pre)begin");
                db.beginTransaction();
                if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                        "PrivacyPersistenceAdapter:deleteSettings: "
                        + "Transaction: (post)begin");
                // make sure this ends up in a consistent state
                try {
                    // try deleting contacts allowed entries; do not fail if deletion
                    // not possible
                    // TODO: restructure this into a more efficient query (ideally a
                    // single query without a cursor)
                    Cursor c = db.query(TABLE_SETTINGS, 
                            new String[] { "_id" }, "packageName=?",
                            new String[] { packageName }, null, null, null);


                    if (c != null && c.getCount() > 0 && c.moveToFirst()) {
                        int id = c.getInt(0);
                        db.delete(TABLE_ALLOWED_CONTACTS, "settings_id=?",
                                new String[] { Integer.toString(id) });
                        c.close();
                    } else {
                        PrivacyDebugger.e(TAG, "deleteSettings - database entry for " 
                                + packageName + " not found");
                    }

                    if (db.delete(TABLE_SETTINGS, "packageName=?", 
                            new String[] { packageName }) == 0) {
                        PrivacyDebugger.e(TAG, "deleteSettings - database entry for " 
                                + packageName + " not found");
                    }

                    // delete settings from plain text file (for access from core
                    // libraries)
                    File settingsPackageDir = new File("/data/system/privacy/" 
                            + packageName + "/");
                    File systemLogsSettingFile = new File("/data/system/privacy/" 
                            + packageName + "/systemLogsSetting");
                    // delete the setting files
                    systemLogsSettingFile.delete();
                    // delete the parent directories
                    if (settingsPackageDir.list() == null || settingsPackageDir.list().length == 0)
                        settingsPackageDir.delete();

                    db.setTransactionSuccessful();
                    mCache.deleteSettings(packageName);
                } finally {
                    if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                            "PrivacyPersistenceAdapter:deleteSettings: "
                            + "Transaction: (pre)end");
                    db.endTransaction();
                    if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                            "PrivacyPersistenceAdapter:deleteSettings: "
                            + "Transaction: (post)end");
                }
            } finally {
                if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                        "PrivacyPersistenceAdapter:deleteSettings: "
                        + "WriteLock: (pre)unlock");
                sDbLock.writeLock().unlock();
                if (LOG_LOCKING) PrivacyDebugger.d(TAG, 
                        "PrivacyPersistenceAdapter:deleteSettings: "
                        + "WriteLock: (post)unlock");
            }
        } catch (SQLiteException e) {
            result = false;
            PrivacyDebugger.e(TAG, 
                    "PrivacyPersistenceAdapter:deleteSettings: failed to open the database, "
                    + "or open a transaction", e);
        } catch (Exception e) {
            result = false;
            PrivacyDebugger.e(TAG, 
                    "PrivacyPersistenceAdapter:deleteSettings - could not delete settings", e);
        } finally {
            Watchdog.onEndAuthorizedTransaction();
            closeIdleDatabase();
        }

        return result;
    }

    private Cursor query(SQLiteDatabase db, String table, String[] columns, String selection,
            String[] selectionArgs, String groupBy, String having, String orderBy, String limit)
            throws Exception {
        Cursor c = null;
        // make sure getting settings does not fail because of
        // IllegalStateException (db already closed)
        boolean success = false;
        for (int i = 0; success == false && i < RETRY_QUERY_COUNT; i++) {
            try {
                if (c != null)
                    c.close();
                c = db.query(table, columns, selection, selectionArgs, groupBy, having, orderBy,
                        limit);
                success = true;
            } catch (IllegalStateException e) {
                success = false;
                closeIdleDatabase();
                announceConnection();
                db = getDatabase();
            }
        }
        if (success == false)
            throw new Exception("query - failed to execute query on the DB");
        return c;
    }

    private Cursor rawQuery(SQLiteDatabase db, String sql) throws Exception {
        Cursor c = null;
        // make sure getting settings does not fail because of
        // IllegalStateException (db already closed)
        boolean success = false;
        for (int i = 0; success == false && i < RETRY_QUERY_COUNT; i++) {
            try {
                if (c != null)
                    c.close();
                c = db.rawQuery(sql, null);
                success = true;
            } catch (IllegalStateException e) {
                success = false;
                closeIdleDatabase();
                announceConnection();
                db = getDatabase();
            }
        }
        if (success == false)
            throw new Exception("query - failed to execute query on the DB");
        return c;
    }

    /**
     * Removes obsolete entries from the DB and file system. Should not be used
     * in methods, which rely on the DB being open after this method has
     * finished. It will close the DB if no other threads has increased the
     * readingThread count.
     * 
     * @return true if purge was successful, false otherwise.
     */
    public boolean purgeSettings() {
        boolean result = true;

        // get installed apps
        Set<String> apps = new HashSet<String>();
        PackageManager pMan = mContext.getPackageManager();
        List<ApplicationInfo> installedApps = pMan.getInstalledApplications(0);
        for (ApplicationInfo appInfo : installedApps) {
            apps.add(appInfo.packageName);
        }

        announceConnection();
        Watchdog.onBeginAuthorizedTransaction();
        SQLiteDatabase db = null;

        try {
            announceConnection();
            if (LOG_OPEN_AND_CLOSE) PrivacyDebugger.d(TAG, 
                    "PrivacyPersistenceAdapter:purgeSettings: "
                    + "Increment DB access threads: now " + Integer.toString(sDbAccessThreads));
            
            // delete obsolete entries from DB and update outdated entries
            db = getDatabase();
            if (db == null) {
                PrivacyDebugger.e(TAG, 
                        "PrivacyPersistenceAdapter:purgeSettings: db could not be obtained");
                return false;
            }

            if (LOG_LOCKING) PrivacyDebugger.d(TAG, 
                    "PrivacyPersistenceAdapter:purgeSettings: "
                    + "WriteLock: (pre)lock");
            sDbLock.writeLock().lock();
            if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                    "PrivacyPersistenceAdapter:purgeSettings: "
                    + "WriteLock: (post)lock");
            try {
                Cursor cursor = null;
                if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                        "PrivacyPersistenceAdapter:purgeSettings: "
                        + "Transaction: (pre)begin");
                db.beginTransaction();
                if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                        "PrivacyPersistenceAdapter:purgeSettings: "
                        + "Transaction: (post)begin");
                try {
                    cursor = query(db, TABLE_SETTINGS, new String[] { "packageName" }, 
                            null, null, null, null, null, null);
                    if (cursor != null && cursor.getCount() > 0 && cursor.moveToFirst()) {
                        do {
                            String packageName = cursor.getString(0);
                            if (!apps.contains(packageName)) {
                                db.delete(TABLE_SETTINGS, "packageName = ?",
                                        new String [] { packageName });
                            }
                        } while (cursor.moveToNext());
                    }

                    // delete obsolete settings directories
                    File settingsDir = new File(SETTINGS_DIRECTORY);
                    for (File packageDir : settingsDir.listFiles()) {
                        String packageName = packageDir.getName();
                        if (!apps.contains(packageName)) {
                            // remove package dir if no such app installed
                            deleteRecursive(packageDir);
                        }
                    }

                    db.setTransactionSuccessful();
                } finally {
                    if (cursor != null) {
                        cursor.close();
                    }
                    if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                            "PrivacyPersistenceAdapter:purgeSettings: "
                            + "Transaction: (pre)end");
                    db.endTransaction();
                    if (LOG_LOCKING) PrivacyDebugger.d(TAG, 
                            "PrivacyPersistenceAdapter:purgeSettings: "
                            + "Transaction: (post)end");
                }
            } finally {
                if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                        "PrivacyPersistenceAdapter:purgeSettings: "
                        + "WriteLock: (pre)unlock");
                sDbLock.writeLock().unlock();
                if (LOG_LOCKING) PrivacyDebugger.d(TAG,
                        "PrivacyPersistenceAdapter:purgeSettings: "
                        + "WriteLock: (post)unlock");
            }
        } catch (Exception e) {
            PrivacyDebugger.e(TAG, 
                    "PrivacyPersistenceAdapter:purgeSettings - purging DB failed", e);
            result = false;
        } finally {
            Watchdog.onEndAuthorizedTransaction();
            closeIdleDatabase();
        }

        return result;
    }

    /**
     * @deprecated
     * @param fileOrDirectory
     */
    private void deleteRecursive(File fileOrDirectory) {
        if (fileOrDirectory.isDirectory()) {
            for (File child : fileOrDirectory.listFiles())
                deleteRecursive(child);
        }
        fileOrDirectory.delete();
    }

    private void createDatabase() {
        PrivacyDebugger.i(TAG, "createDatabase - creating privacy database file");
        Watchdog.onBeginAuthorizedTransaction();
        try {
            SQLiteDatabase db = SQLiteDatabase.openDatabase(DATABASE_FILE, null,
                    SQLiteDatabase.OPEN_READWRITE | SQLiteDatabase.CREATE_IF_NECESSARY);
            PrivacyDebugger.i(TAG, "createDatabase - creating privacy database");
            db.execSQL(CREATE_TABLE_SETTINGS);
            db.execSQL(CREATE_TABLE_ALLOWED_CONTACTS);
            db.execSQL(CREATE_TABLE_MAP);
            db.execSQL(INSERT_VERSION);
            db.execSQL(INSERT_ENABLED);
            db.execSQL(INSERT_NOTIFICATIONS_ENABLED);
            // PrivacyDebugger.d(TAG, "createDatabase - closing connection to privacy.db");
            if (db != null && db.isOpen())
                db.close();
        } catch (SQLException e) {
            PrivacyDebugger.e(TAG, "createDatabase - failed to create privacy database", e);
        } finally {
            Watchdog.onEndAuthorizedTransaction();
    }

    /**
     * @author: CollegeDev
     */
    @Override
    public void onUnauthorizedDatabaseAccess(int msg) {

        if(isFailSafeActive()) return; //prevents hammering -> only oneshot possible
        //make sure you only call thread safe methods!
        try {
            setFailSafeMode(true);
            Watchdog.onBeginAuthorizedTransaction();
            // inform user first
            Intent intent = new Intent();
            Intent backup = new Intent();
            PrivacyDebugger.e(TAG,"recognized unauthorized databaseaccess. Reason: " + Watchdog.msgToString(msg));
            intent.setAction(PrivacySettingsManager.ACTION_FAIL_SAFE_MODE_TRIGGERED);
            intent.putExtra(PrivacyWatchdog.MSG_WHAT_INT, msg);
            intent.putExtra(PrivacyWatchdog.MSG_WHAT_STRING, Watchdog.msgToString(msg));
            context.sendBroadcast(intent, RECEIVE_FAIL_SAFE_TRIGGERED);

            // try to handle our self!
           deleteCompleteSettings();
            reinitAll();
            //once again to be sure!
            Watchdog.startWatching();
            //now try to recover
            ArrayList<String> recovery = tryRecoverFromCache();

            //inform user!
            if(recovery.isEmpty()) { 
                backup.setAction(PrivacySettingsManager.ACTION_FAIL_SAFE_BACKUP_COMPLETE);
                context.sendBroadcast(backup, RECEIVE_FAIL_SAFE_TRIGGERED);
            } else {// some settings can't be saved, inform user about that!
                backup.putStringArrayListExtra(PrivacyWatchdog.MSG_RECOVERY_FAIL_INFO, recovery);
                backup.setAction(PrivacySettingsManager.ACTION_FAIL_SAFE_BACKUP_FAILED);
                context.sendBroadcast(backup, RECEIVE_FAIL_SAFE_TRIGGERED);
            }
        } catch (Exception e) {
            PrivacyDebugger.e(TAG,"something went totally wrong in onUnauthorizedDatabaseAccess()");
        } finally {
            Watchdog.onEndAuthorizedTransaction();
        }
    }

    /**
     * @author: CollegeDev
     */
    @Override
    public void onWatchdogFinalize(boolean authorizedAccessInProgress) {
        PrivacyDebugger.w(TAG,"got information that Watchdog is dead, initiate a new one!");
        Watchdog = new PrivacyWatchdog(this, authorizedAccessInProgress);
    }

    private void createSettingsDir() {
        // create settings directory (for settings accessed from core libraries)
        File settingsDir = new File("/data/system/privacy/");
        settingsDir.mkdirs();
        // make it readable for everybody
        settingsDir.setReadable(true, false);
        settingsDir.setExecutable(true, false);
    }

    private synchronized SQLiteDatabase getDatabase() {
        if (mDb == null || !mDb.isOpen() || mDb.isReadOnly()) {
            if (LOG_OPEN_AND_CLOSE) PrivacyDebugger.d(TAG,
                    "PrivacyPersistenceAdapter:closeIdleDatabase: "
                    + "Opening privacy database");
            mDb = SQLiteDatabase.openDatabase(DATABASE_FILE, null, SQLiteDatabase.OPEN_READWRITE);
        }   
        return mDb;
    }

    /**
     * 
     * @return true if failsafemode is active, false otherwise
     */
    public boolean isFailSafeActive () {
        return isFailSaveActive;
    }

    /**
     * Only call it after boot is ready and failSafeMode was not deactivated by user or to deactivate the fail safe mode
     * @param state true -> activates the failSafeMode, false -> deactivates the failSafeMode
     */
    public void setFailSafeMode(boolean state) {
        PrivacyDebugger.w(TAG,"setFailSafeMode() got a call, do you really want that?!");
        isFailSaveActive = state;
    }

    /**
     * Fills the complete cache with all data from database
     * Only call this method in constructor
     */
    private synchronized void fillPrivacyCache() {
        PrivacyDebugger.i(TAG, "on entry fillPrivacyCache()");
        List<ApplicationInfo> apps = context.getPackageManager().getInstalledApplications(0);
        for (ApplicationInfo appInfo : apps) { 
            PrivacyDebugger.i(TAG,"filling cache for package: " + appInfo.packageName);
            getSettings(appInfo.packageName, true); //only call it 
        }
        PrivacyDebugger.i(TAG,"on exit fillPrivacyCache()");
    }

    /**
     * Deletes the given folder or files and all sub-directories with files
     * @param path path t
     */
    private void removeFiles(String path) {
        File file = new File(path);
        PrivacyDebugger.w(TAG, "deleting now file(s) or folder(s): " + file.getAbsolutePath());
        if (file.exists()) {
            String cmd = "rm -r " + path;
            Runtime runtime = Runtime.getRuntime();
            try {
                runtime.exec(cmd);
                PrivacyDebugger.i(TAG, "deleted file(s) or folder(s) successful");
            } catch (IOException e) { 
                PrivacyDebugger.e(TAG, "Got IOException while trying to delete file(s) or folder(s)", e);
            } catch (Exception e) {
                PrivacyDebugger.e(TAG, "Got Exception while trying to delete file(s) or folder(s)", e);
            }
        } else {
            PrivacyDebugger.e(TAG,"can't delete file(s) or folder(s) for path: " + file.getAbsolutePath()
                    + " because it doesn't exists");
        }
    }
    
    /**
     * Deletes all PrivacySettings files:
     *      - Database 
     *      - Database journal file
     *      - Settingsdirectory
     *  It also stops monitoring on privacy.db (for Watchdog)
     */
    private void deleteCompleteSettings() {
        if(Watchdog != null) 
            Watchdog.stopWatching();
        removeFiles(DATABASE_JOURNAL_FILE);
        removeFiles(DATABASE_FILE);
        removeFiles(SETTINGS_DIRECTORY);
    }

    /**
     * Recovers all settings from current cache to database. Call this method 
     * if database base is empty only!
     * @return true, if <b>all</b> settings have been successful saved, false otherwise
     */
    private ArrayList<String> tryRecoverFromCache() {
        ArrayList<String> output = new ArrayList<String>();
        announceConnection();
        sDbLock.writeLock().lock();
        Watchdog.onBeginAuthorizedTransaction();
        mCache.markAllAsNewEntry();
        PrivacyDebugger.i(TAG,"now trying to recover settings from cache!");
        try {
            // TODO: speed this up by leaving the database open!!
            ArrayList<PrivacySettings> settings = mCache.getAllSetings();
            for(PrivacySettings insertion : settings) {
                if(!saveSettings(insertion)) {
                    output.add(insertion.getPackageName());
                    PrivacyDebugger.e(TAG,"restore failed for package: " + insertion.getPackageName());
                } 
            }
            mCache.removeAll();
            if(settings.size() == output.size()) {
                PrivacyDebugger.e(TAG, "nothing can't be restore :-! ?");
            } else {
                fillPrivacyCache();
            }

        } catch (Exception e) {
            PrivacyDebugger.e(TAG,"something went wrong while trying to recover settings from cache "
                    + "after unauthorized database access!");

        } finally {
            if(output.isEmpty())
                PrivacyDebugger.i(TAG,"successful recovered ALL settings from cache");
            else 
                PrivacyDebugger.e(TAG, "wasn't able to recover all settings?!");
            Watchdog.onEndAuthorizedTransaction();
            sDbLock.writeLock().unlock();
            closeIdlingDatabase();
        }
        return output;
    }

    /**
     * Call this method right before you lock the read or write access
     */
    private void announceConnection() {
        int threads = dbThreads.incrementAndGet();
        PrivacyDebugger.i(TAG, "current amount of dbThreads: " + threads);
    }

    /**
     * If there are no more threads reading the database, close it. Otherwise,
     * reduce the number of reading threads by one
     */
    private void closeIdleDatabase() {
        int threads = (sDbAccessThreads.get() > 0) ? sDbAccessThreads.decrementAndGet() : 0;
        PrivacyDebugger.i(TAG,"amount of database threads: " + threads);
        // only close DB if no other threads are reading
        if (sDbAccessThreads == 0 && mDb != null && mDb.isOpen()) {
            if (autoCloseDb) {
                if (LOG_OPEN_AND_CLOSE) PrivacyDebugger.d(TAG,
                        "PrivacyPersistenceAdapter:"
                        + "closeIdleDatabase: Closing the PDroid database");
                mDb.close();
            } else {
                if (LOG_OPEN_AND_CLOSE) PrivacyDebugger.d(TAG, 
                        "PrivacyPersistenceAdapter:"
                        + "closeIdleDatabase: Open and close DB disabled: not closing");
            }
        }
    }

    /**
     * Reinit the whole set (privacy db, privacy settings dir, ...)
     * Only call this method after you called the deleteCompleteSettings() method!
     * this also triggers the Watchdog to watch on privacy.db
     *
     * @author: CollegeDev
     */
    private void reinitAll() {
        boolean canWrite = new File("/data/system/").canWrite();
        PrivacyDebugger.i(TAG, "called reinitAll() - canWrite: " + canWrite);
        if (canWrite) {
            PrivacyDebugger.i(TAG,"we're able to write, create complete new set now");
            announceConnection();
            sDbLock.writeLock().lock();
            Watchdog.onBeginAuthorizedTransaction();
            try {
                if (!new File(DATABASE_FILE).exists()) 
                    createDatabase();
                if(Watchdog != null)
                    Watchdog.startWatching();
                if (!new File(SETTINGS_DIRECTORY).exists()) 
                    createSettingsDir();
                int currentVersion = getDbVersion();
                PrivacyDebugger.d(TAG, "PrivacyPersistenceAdapter - current DB version: " + currentVersion);
                if (currentVersion < DATABASE_VERSION) 
                    upgradeDatabase(currentVersion);

            } catch(Exception e) {
                PrivacyDebugger.e(TAG, "got exception while trying to create database and/or "
                        + "settingsDirectories for reinitializing!");
            } finally {
                PrivacyDebugger.i(TAG,"successful reinitialized the whole set");
                Watchdog.onEndAuthorizedTransaction();
                sDbLock.writeLock().unlock();
                closeIdlingDatabase();
            }
        }
    }


}
