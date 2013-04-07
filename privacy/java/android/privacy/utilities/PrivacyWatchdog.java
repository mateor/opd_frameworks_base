package android.privacy;

import android.os.FileObserver;
import android.privacy.utilities.PrivacyDebugger;
/**
 * Copyright (C) 2012-2013 Stefan Thiele (CollegeDev)
 * This program is free software; you can redistribute it and/or modify it under
 * the terms of the GNU General Public License as published by the Free Software
 * Foundation; either version 3 of the License, or (at your option) any later version.
 * This program is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
 * PARTICULAR PURPOSE. See the GNU General Public License for more details.
 * You should have received a copy of the GNU General Public License along with
 * this program; if not, see <http://www.gnu.org/licenses>.
 */
public final class PrivacyWatchDog extends FileObserver {

    private static final String TAG = "PrivacyWatchDog";

    private static final String WATCH_PATH = "/data/system/privacy.db";

    private PrivacyWatchDogInterface callBack;

    /**
     * intent data key
     */
    public static final String MSG_WHAT_INT = "msg_what_i";

    /**
     * intent data key
     */
    public static final String MSG_WHAT_STRING = "msg_what_s";

    /**
     * intent data key, this key contains an ArrayList with all packageNames inside for which
     * we wasn't able to restore the settings.
     */
    public static final String MSG_RECOVERY_FAIL_INFO = "rc_info";

    /**
     * MSG will be attached in callBack if someone changed the database
     */
    public static final int MSG_DATABASE_MODIFY = 1;
    /**
     * MSG will be attached in CallBack if someone deleted the database
     */
    public static final int MSG_DATABASE_DELETED = 2;
    /**
     * MSG will be attached in CallBack if someone moved the database
     */
    public static final int MSG_DATABASE_MOVED = 3;


    private boolean authorizedSave = false;
    
    /**
     * Constructor
     * @param iface current callBack interface
     */
    public PrivacyWatchDog(PrivacyWatchDogInterface iface) {
        super(WATCH_PATH);
        callBack = iface;
        PrivacyDebugger.i(TAG,"initalized watchdog!");
        this.startWatching();
        PrivacyDebugger.i(TAG,"started watching on database");
    }

    /**
     * Use this constructor if the onWatchDogFinalize callback gets a call.
     * It can happen that the watchdog gets finalize during an authorized db access, 
     * @param iface
     * @param authorizedAccessInProgress 
     *      true if currently there is one authorized access in progress, false otherwise
     */
    public PrivacyWatchDog(PrivacyWatchDogInterface iface, boolean 
            authorizedAccessInProgress) {
        super(WATCH_PATH);
        callBack = iface;
        PrivacyDebugger.i(TAG,"Constructor called because watchdog finalized."
                + "AuthorizedAccessinProgress: " + authorizedAccessInProgress);
        if(authorizedAccessInProgress)
            authorizedSave = true;
        this.startWatching();
        PrivacyDebugger.i(TAG,"started watching on database");
    }

    /**
     * Sets the current interface
     * @param iface current callBack interface
     */
    public void setInterface(PrivacyWatchDogInterface iface) {
        callBack = iface;
    }

    @Override
    public void onEvent(int event, String path) {

        //data was written to a file
        if ((FileObserver.MODIFY & event) != 0) {
            PrivacyDebugger.w(TAG, "detected database modified");
            if(!authorizedSave) {
                PrivacyDebugger.w(TAG, "inform adapter about modified database");
                callBack.onUnauthorizedDatabaseAccess(MSG_DATABASE_MODIFY);
            } else {
                PrivacyDebugger.i(TAG, "user is authorized to modify database, "
                        + "do not inform adapter!");
            }
        }
        //the monitored file or directory was deleted, monitoring effectively stops
        if ((FileObserver.DELETE_SELF & event) != 0) {
            PrivacyDebugger.w(TAG, "detected database deleted");
            callBack.onUnauthorizedDatabaseAccess(MSG_DATABASE_DELETED);
        }
        //the monitored file or directory was moved; monitoring continues
        if ((FileObserver.MOVE_SELF & event) != 0) {
            PrivacyDebugger.w(TAG, "detected database moved");
            callBack.onUnauthorizedDatabaseAccess(MSG_DATABASE_MOVED);
        }

    }

    @Override
    public void finalize () {
        // shit-> inform service about that :-/
        try {
            callBack.onWatchDogFinalize(authorizedSave);
        } catch(Exception e) {
            PrivacyDebugger.e(TAG, "can't inform that WatchDog g finalized!", e);
        }
        try {
            super.finalize();
        } catch(Exception e) {
            //nothing here
        }
    }

    /**
     * Call this method at the beginning of authorized database accesses
     */
    public synchronized void onBeginAuthorizedTransaction() {
        authorizedSave = true;
    }

    /**
     * Call this method at the end of authorized database accesses
     */
    public synchronized void onEndAuthorizedTransaction() {
        authorizedSave = false;
    }

    /**
     * Converts callBack message to readable string
     * @param msg callBack message
     * @return readable string for debug or whatever
     */
    public String msgToString (int msg) {
        switch(msg) {
            case MSG_DATABASE_MODIFY:
                return "database modified";
            case MSG_DATABASE_DELETED:
                return "database deleted";
            case MSG_DATABASE_MOVED:
                return "database moved";
            default:
                return "UNKNOWN";
        }
    }

    /**
     * WatchDog interface to handle UnauthorizedDatabaseAccesses
     * @author CollegeDev
     */
    public interface PrivacyWatchDogInterface {

        /**
         * This method gets a call if someone tries to:
         *      - Write to database and modifying permissions
         *      - delete the database 
         *      - moving the database
         */
        public void onUnauthorizedDatabaseAccess(int MSG_WHAT);
        

        /**
         * This method gets a call if our current watchDog gets finalize
         * -> WatchDog is stops watching, we have to initiate a new one
         * @param authorizedAccessInProgress is the last state of our 
         *                                      internal authorizedSave variable
         */
        public void onWatchDogFinalize(boolean authorizedAccessInProgress);

    }

}
