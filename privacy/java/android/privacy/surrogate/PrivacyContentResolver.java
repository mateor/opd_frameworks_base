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

package android.privacy.surrogate;

import android.content.Context;
import android.content.IContentProvider;
import android.database.Cursor;
import android.net.Uri;
import android.os.Binder;
import android.os.RemoteException;
import android.privacy.PrivacyServiceException;
import android.privacy.PrivacySettings;
import android.privacy.PrivacySettingsManager;
import android.provider.Browser;
import android.provider.CalendarContract;
import android.provider.CallLog;
import android.provider.ContactsContract;
import android.privacy.utilities.PrivacyDebugger;
import android.util.Log;

/**
 * Provides privacy handling for {@link android.content.ContentResolver}
 * @author Svyatoslav Hresyk 
 * {@hide}
 */
public final class PrivacyContentResolver {

    private static final String TAG = "PrivacyContentResolver";

    private static final String SMS_CONTENT_URI_AUTHORITY = "sms";
    private static final String MMS_CONTENT_URI_AUTHORITY = "mms";
    private static final String MMS_SMS_CONTENT_URI_AUTHORITY = "mms-sms";

    private static PrivacySettingsManager pSetMan;

    /**
     * Returns a dummy database cursor if access is restricted by privacy settings
     * @param uri
     * @param context
     * @param realCursor
     */
    public static Cursor enforcePrivacyPermission(Uri uri, String[] projection, Context context, Cursor realCursor) throws RemoteException {
        //    public static Cursor enforcePrivacyPermission(Uri uri, Context context, Cursor realCursor) {
        if (uri != null) {
            String auth = uri.getAuthority();
            String output_label = "[real]";
            Cursor output = realCursor;
            if (auth != null) {
                if (auth.equals(android.provider.Contacts.AUTHORITY) || auth.equals(ContactsContract.AUTHORITY)) {

                    if (pSetMan == null) pSetMan = PrivacySettingsManager.getPrivacyService(context);
                    String packageName = context.getPackageName();
                    try {
                        PrivacySettings pSet = pSetMan.getSettings(packageName);
                        if (pSet == null || pSet.getContactsSetting() == PrivacySettings.REAL) {
                            pSetMan.notification(packageName, PrivacySettings.REAL, PrivacySettings.DATA_CONTACTS, null);
                        } else if (pSet.getContactsSetting() == PrivacySettings.EMPTY) {
                            output_label = "[empty]";
                            output = new PrivacyCursor();
                            pSetMan.notification(packageName, PrivacySettings.EMPTY, PrivacySettings.DATA_CONTACTS, null);
                        } else if (pSet.getContactsSetting() == PrivacySettings.CUSTOM && 
                                uri.toString().contains(ContactsContract.Contacts.CONTENT_URI.toString())) {

                            boolean idFound = false;
                            if (projection != null) {
                                for (String p : projection) {
                                    if (p.equals(ContactsContract.Contacts._ID)) {
                                        idFound = true;
                                        break;
                                    }
                                }
                            }

                            if (!idFound) {
                                output = new PrivacyCursor();
                            } else {
                                output = new PrivacyCursor(output, pSet.getAllowedContacts());
                            }
                            pSetMan.notification(packageName, PrivacySettings.CUSTOM, PrivacySettings.DATA_CONTACTS, null);
                        }
                    } catch (PrivacyServiceException e) {
                        output_label = "[empty]";
                        output = new PrivacyCursor();
                        pSetMan.notification(packageName, PrivacySettings.ERROR, PrivacySettings.DATA_CONTACTS, null);
                    } catch (NullPointerException e) {
                        PrivacyDebugger.e(TAG, "PrivacyContentResolver:"
                            + "enforcePrivacyPermissions: NullPointerException occurred, "
                            + "probably privacy service", e);
                        output_label = "[empty]";
                        output = new PrivacyCursor();
                    }
                } else if (auth.equals(CalendarContract.AUTHORITY)) {
                    if (pSetMan == null) pSetMan = PrivacySettingsManager.getPrivacyService(context);
                    String packageName = context.getPackageName();
                    try {
                        PrivacySettings pSet = pSetMan.getSettings(packageName);
                        if (pSet == null || pSet.getCalendarSetting() == PrivacySettings.REAL) {
                            pSetMan.notification(packageName, PrivacySettings.REAL, PrivacySettings.DATA_CALENDAR, null);
                        } else {
                            output_label = "[empty]";
                            output = new PrivacyCursor();
                            pSetMan.notification(packageName, PrivacySettings.EMPTY, PrivacySettings.DATA_CALENDAR, null);
                        }
                    } catch (PrivacyServiceException e) {
                        output_label = "[empty]";
                        output = new PrivacyCursor();
                        pSetMan.notification(packageName, PrivacySettings.ERROR, PrivacySettings.DATA_CALENDAR, null);
                    } catch (NullPointerException e) {
                        PrivacyDebugger.e(TAG, "PrivacyContentResolver:"
                            + "enforcePrivacyPermissions: NullPointerException occurred, "
                            + "probably privacy service", e);
                        output_label = "[empty]";
                        output = new PrivacyCursor();
                    }

                } else if (auth.equals(MMS_CONTENT_URI_AUTHORITY)) {
                    if (pSetMan == null) pSetMan = PrivacySettingsManager.getPrivacyService(context);
                    String packageName = context.getPackageName();
                    try {
                        PrivacySettings pSet = pSetMan.getSettings(packageName);
                        if (pSet == null || pSet.getMmsSetting() == PrivacySettings.REAL) {
                            pSetMan.notification(packageName, PrivacySettings.REAL, PrivacySettings.DATA_MMS, null);
                        } else {
                            output_label = "[empty]";
                            output = new PrivacyCursor();
                            pSetMan.notification(packageName, PrivacySettings.EMPTY, PrivacySettings.DATA_MMS, null);
                        }
                    } catch (PrivacyServiceException e) {
                        output_label = "[empty]";
                        output = new PrivacyCursor();
                        pSetMan.notification(packageName, PrivacySettings.ERROR, PrivacySettings.DATA_MMS, null);
                    } catch (NullPointerException e) {
                        PrivacyDebugger.e(TAG, "PrivacyContentResolver:"
                            + "enforcePrivacyPermissions: NullPointerException occurred, "
                            + "probably privacy service", e);
                        output_label = "[empty]";
                        output = new PrivacyCursor();
                    }

                } else if (auth.equals(SMS_CONTENT_URI_AUTHORITY)) {
                    if (pSetMan == null) pSetMan = PrivacySettingsManager.getPrivacyService(context);
                    String packageName = context.getPackageName();
                    try {
                        PrivacySettings pSet = pSetMan.getSettings(packageName);
                        if (pSet == null || pSet.getSmsSetting() == PrivacySettings.REAL) {
                            pSetMan.notification(packageName, PrivacySettings.REAL, PrivacySettings.DATA_SMS, null);
                        } else {
                            output_label = "[empty]";
                            output = new PrivacyCursor();
                            pSetMan.notification(packageName, PrivacySettings.EMPTY, PrivacySettings.DATA_SMS, null);
                        }
                    } catch (PrivacyServiceException e) {
                        output_label = "[empty]";
                        output = new PrivacyCursor();
                        pSetMan.notification(packageName, PrivacySettings.ERROR, PrivacySettings.DATA_SMS, null);
                    } catch (NullPointerException e) {
                        PrivacyDebugger.e(TAG, "PrivacyContentResolver:"
                            + "enforcePrivacyPermissions: NullPointerException occurred, "
                            + "probably privacy service", e);
                        output_label = "[empty]";
                        output = new PrivacyCursor();
                    }
                    // all messages, sms and mms
                } else if (auth.equals(MMS_SMS_CONTENT_URI_AUTHORITY) || 
                        auth.equals("mms-sms-v2") /* htc specific, accessed by system messages application */) { 

                    // deny access if access to either sms, mms or both is restricted by privacy settings
                    if (pSetMan == null) pSetMan = PrivacySettingsManager.getPrivacyService(context);
                    String packageName = context.getPackageName();
                    try {
                        PrivacySettings pSet = pSetMan.getSettings(packageName);
                        if (pSet == null || (pSet.getMmsSetting() == PrivacySettings.REAL && pSet.getSmsSetting() == PrivacySettings.REAL)) {
                            pSetMan.notification(packageName, PrivacySettings.REAL, PrivacySettings.DATA_MMS_SMS, null);
                        } else {
                            output_label = "[empty]";
                            output = new PrivacyCursor();
                            pSetMan.notification(packageName, PrivacySettings.EMPTY, PrivacySettings.DATA_MMS_SMS, null);
                        }
                    } catch (PrivacyServiceException e) {
                        output_label = "[empty]";
                        output = new PrivacyCursor();
                        pSetMan.notification(packageName, PrivacySettings.ERROR, PrivacySettings.DATA_MMS_SMS, null);
                    } catch (NullPointerException e) {
                        PrivacyDebugger.e(TAG, "PrivacyContentResolver:"
                            + "enforcePrivacyPermissions: NullPointerException occurred, "
                            + "probably privacy service", e);
                        output_label = "[empty]";
                        output = new PrivacyCursor();
                    }
                } else if (auth.equals(CallLog.AUTHORITY)) {
                    if (pSetMan == null) pSetMan = PrivacySettingsManager.getPrivacyService(context);
                    String packageName = context.getPackageName();
                    try {
                        PrivacySettings pSet = pSetMan.getSettings(packageName);
                        if (pSet == null || pSet.getCallLogSetting() == PrivacySettings.REAL) {
                            pSetMan.notification(packageName, PrivacySettings.REAL, PrivacySettings.DATA_CALL_LOG, null);
                        } else {
                            output_label = "[empty]";
                            output = new PrivacyCursor();
                            pSetMan.notification(packageName, PrivacySettings.EMPTY, PrivacySettings.DATA_CALL_LOG, null);
                        }
                    } catch (PrivacyServiceException e) {
                        output_label = "[empty]";
                        output = new PrivacyCursor();
                        pSetMan.notification(packageName, PrivacySettings.ERROR, PrivacySettings.DATA_CALL_LOG, null);
                    } catch (NullPointerException e) {
                        PrivacyDebugger.e(TAG, "PrivacyContentResolver:"
                            + "enforcePrivacyPermissions: NullPointerException occurred, "
                            + "probably privacy service", e);
                        output_label = "[empty]";
                        output = new PrivacyCursor();
                    }

                } else if (auth.equals(Browser.BOOKMARKS_URI.getAuthority())) {
                    if (pSetMan == null) pSetMan = PrivacySettingsManager.getPrivacyService(context);
                    String packageName = context.getPackageName();
                    try {
                        PrivacySettings pSet = pSetMan.getSettings(packageName);
                        if (pSet == null || pSet.getBookmarksSetting() == PrivacySettings.REAL) {
                            pSetMan.notification(packageName, PrivacySettings.REAL, PrivacySettings.DATA_BOOKMARKS, null);
                        } else {                            
                            output_label = "[empty]";
                            output = new PrivacyCursor();
                            pSetMan.notification(packageName, PrivacySettings.EMPTY, PrivacySettings.DATA_BOOKMARKS, null);
                        }
                    } catch (PrivacyServiceException e) {
                        output_label = "[empty]";
                        output = new PrivacyCursor();
                        pSetMan.notification(packageName, PrivacySettings.ERROR, PrivacySettings.DATA_BOOKMARKS, null);
                    } catch (NullPointerException e) {
                        PrivacyDebugger.e(TAG, "PrivacyContentResolver:"
                            + "enforcePrivacyPermissions: NullPointerException occurred, "
                            + "probably privacy service", e);
                        output_label = "[empty]";
                        output = new PrivacyCursor();
                    }
                }
            }
            return output;
        }
        return realCursor;
    }

    private static String arrayToString(String[] array) {
        StringBuffer sb = new StringBuffer();
        if (array != null) for (String bla : array) sb.append("[" + bla + "]");
        else return "";
        return sb.toString();
    }
    /**
     * This method is especially for faking android_id if google wants to read it in their privacy database
     * @author CollegeDev
     * @param uri
     * @param projection
     * @param context
     * @param realCursor
     */
    public static Cursor enforcePrivacyPermission(Uri uri, String[] projection, Context context, Cursor realCursor, boolean google_access) throws RemoteException {
        if (uri != null) {
            String auth = uri.getAuthority();
            String output_label = "[real]";
            Cursor output = realCursor;
            if (auth != null && auth.equals("com.google.android.gsf.gservices")) {
                boolean privacyAllowed = false;
                String packageName = context.getPackageName();
                if (pSetMan == null) pSetMan = PrivacySettingsManager.getPrivacyService(context);
                if (pSetMan == null) {
                    PrivacyDebugger.e(TAG,"PrivacyContentResolver:"
                        + "enforcePrivacyPermission: privacy service could not be obtained");
                } else {
                    try {
                        PrivacySettings pSet = pSetMan.getSettings(packageName);
                        if (pSet == null || pSet.getSimInfoSetting() == PrivacySettings.REAL){
                            privacyAllowed = true;
                        } else  {
                            privacyAllowed = false;
                        }
                    } catch (PrivacyServiceException e) {
                        privacyAllowed = false;
                    } catch (NullPointerException e) {
                        PrivacyDebugger.e(TAG, "PrivacyContentResolver:"
                            + "enforcePrivacyPermissions: NullPointerException occurred, "
                            + "probably privacy service", e);
                        privacyAllowed = false;
                    }
                }
                
                if (privacyAllowed) {
                    PrivacyDebugger.i(TAG,"google is allowed to get real cursor");
                    pSetMan.notification(packageName, PrivacySettings.REAL, PrivacySettings.DATA_NETWORK_INFO_SIM, null);
                } else {
                    int actual_pos = realCursor.getPosition();
                    int forbidden_position = -1;
                    try{
                        for(int i=0;i<realCursor.getCount();i++){
                            realCursor.moveToNext();
                            if(realCursor.getString(0).equals("android_id")){
                                forbidden_position = realCursor.getPosition();
                                break;
                            }
                        }
                    } catch (Exception e){
                        PrivacyDebugger.e(TAG,"something went wrong while getting blocked "
                            + "permission for android id");
                    } finally{
                        realCursor.moveToPosition(actual_pos);
                        if(forbidden_position == -1) {PrivacyDebugger.i(TAG,
                            "now we return real cursor, because forbidden_pos is -1"); 
                            return output;} //give realcursor, there's no android_id to block
                    }
                    PrivacyDebugger.i(TAG,"now blocking google access to android id and "
                        + "give fake cursor. forbidden_position: " + forbidden_position);
                    output_label = "[fake]";
                    output = new PrivacyCursor(realCursor,forbidden_position);
                    pSetMan.notification(packageName, PrivacySettings.EMPTY, PrivacySettings.DATA_NETWORK_INFO_SIM, null);
                }
            }
            return output;
        }
        return realCursor;   
    }
}
