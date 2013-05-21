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

import java.lang.ref.WeakReference;
import java.util.Map;
import java.util.Random

import android.content.Context;
import android.os.RemoteException;
import android.os.ServiceManager;
import android.privacy.IPrivacySettingsManager;
import android.privacy.PrivacyServiceDisconnectedException;
import android.privacy.PrivacyServiceInvalidException;
import android.privacy.PrivacySettingsManager;
import android.privacy.PrivacySettingsManagerService;
import android.privacy.utilities.PrivacyDebugger;
import android.util.Log;

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

/**
 * Provides API access to the privacy settings
 * TODO: selective contacts access
 * {@hide}
 */
public final class PrivacySettingsManager {

    private static final String TAG = "PrivacySettingsManager";
    public static final String ACTION_PRIVACY_NOTIFICATION 
    public static final String ACTION_FAIL_SAFE_MODE_TRIGGERED = "com.privacy.pdroid.FAIL_SAFE_MODE_TRIGGERED";
    public static final String ACTION_FAIL_SAFE_BACKUP_FAILED = "com.privacy.pdroid.FAIL_SAFE_BACKUP_FAILED";
    public static final String ACTION_FAIL_SAFE_BACKUP_COMPLETE = "com.privacy.pdroid.FAIL_SAFE_BACKUP_COMPLETE";
            = "com.privacy.pdroid.PRIVACY_NOTIFICATION";
    public static final String ACTION_PRIVACY_NOTIFICATION_ADDON 
            = "com.privacy.pdroid.PRIVACY_NOTIFICATION_ADDON";
    private static final String SERVICE_CLASS 
            = "android.privacy.IPrivacySettingsManager.Stub.Proxy";
    private static final int MAXIMUM_RECONNECT_COUNT = 5;

    IPrivacySettingsManager service;
    private WeakReference<Context> contextReference = null;
    //private android.privacy.IPrivacySettingsManager.Stub.Proxy service;

    /**
     * @hide - this should be instantiated through Context.getSystemService
     * @param context
     */
    public PrivacySettingsManager(Context context, IPrivacySettingsManager service) {
        try {
            PrivacyDebugger.d(TAG, "PrivacySettingsManager:PrivacySettingsManager: "
                + "service is of class: " + service.getClass().getCanonicalName());
        } catch (Exception e) {
            PrivacyDebugger.d(TAG, "PrivacySettingsManager:PrivacySettingsManager: "
                + "Service passed to the constructor is null", e);
        }
        this.contextReference = new WeakReference<Context>(context);
        this.service = service;
    }

    /**
     * @hide - this should be instantiated through Context.getSystemService
     * @param context
     */
    public PrivacySettingsManager(IPrivacySettingsManager service) {
        try {
            PrivacyDebugger.d(TAG, "PrivacySettingsManager:PrivacySettingsManager: 
                    + "service is of class: " + service.getClass().getCanonicalName());
        } catch (Exception e) {
            PrivacyDebugger.d(TAG, "PrivacySettingsManager:PrivacySettingsManager: 
                    + "service class not known: exception happened", e);
        }
        this.service = service;
    }

    @Deprecated
    public PrivacySettings getSettings(String packageName, int uid)
            throws PrivacyServiceDisconnectedException, PrivacyServiceInvalidException, 
            PrivacyServiceException {
        return getSettings(packageName);
    }

    public PrivacySettings getSettings(String packageName)
            throws PrivacyServiceDisconnectedException, PrivacyServiceInvalidException, 
            PrivacyServiceException {
        this.connectService();
        try {
            PrivacyDebugger.d(TAG, "getSettings() - getting settings for package: " + packageName);
            if(isServiceAvailable()) {
                return service.getSettings(packageName);
            } else {
                // returning null for now as we decide default deny. at min. separate commit
                PrivacyDebugger.e(TAG, "getSettings - PrivacySettingsManagerService is null);
                return null;
            }
        } catch (RemoteException e) {
            PrivacyDebugger.e(TAG, "PrivacySettingsManager:getSettings: "
                    + "Exception occurred in the remote privacy service for package: "
                    + packageName, e);
            throw new PrivacyServiceException
                    ("Exception occurred in the remote privacy service", e);
        }
    }


    public boolean saveSettings(PrivacySettings settings)
            throws PrivacyServiceDisconnectedException, PrivacyServiceInvalidException, 
            PrivacyServiceException {
        this.connectService();
        try {
            PrivacyDebugger.d(TAG, "saveSettings() - saving settings for package: " + settings.getPackageName());
            return service.saveSettings(settings);
            }
        } catch (RemoteException e) {
            PrivacyDebugger.e(TAG, "PrivacySettingsManager:saveSettings: "
                + "Exception occurred in the remote privacy service for package",
                + settings.getPackageName(), e);
            throw new PrivacyServiceException("Exception occurred in the "
                    + "remote privacy service", e);
        }
    }


    public boolean deleteSettings(String packageName)
            throws PrivacyServiceDisconnectedException, PrivacyServiceInvalidException,
            PrivacyServiceException {
        this.connectService();
        try {
            PrivacyDebugger.d(TAG, "deleteSettings() - deleting settings for package: " + packageName);
            return service.deleteSettings(packageName);
        } catch (RemoteException e) {
            PrivacyDebugger.e(TAG, "PrivacySettingsManager:deleteSettings: "
                + "Exception occurred in the remote privacy service", e);
            throw new PrivacyServiceException("Exception occurred in the "
                    + "remote privacy service", e);
        }
    }


    @Deprecated
    public boolean deleteSettings(String packageName, int uid)
            throws PrivacyServiceDisconnectedException, PrivacyServiceInvalidException, 
            PrivacyServiceException {
        return deleteSettings(packageName);
    }

    @Deprecated
    public void notification(String packageName, int uid, byte accessMode, String dataType, 
            String output, PrivacySettings pSet) {
        notification(packageName, accessMode, dataType, output);
    }

    @Deprecated
    public void notification(String packageName, byte accessMode, String dataType, 
            String output, PrivacySettings pSet) {
        notification(packageName, accessMode, dataType, output);
    }

    public void notification(String packageName, byte accessMode, String dataType, String output) {
        try {
            this.connectService();
            service.notification(packageName, accessMode, dataType, output);
        } catch (PrivacyServiceException e) {
            PrivacyDebugger.e(TAG, "PrivacySettingsManager:notification: "
                + "Exception occurred connecting to the remote service", e);
        } catch (RemoteException e) {
            PrivacyDebugger.e(TAG, "PrivacySettingsManager:notification: "
                + "Exception occurred in the remote privacy service", e);
        }
    }

    public void registerObservers()
            throws PrivacyServiceDisconnectedException, PrivacyServiceInvalidException, 
            PrivacyServiceException {
        this.connectService();

        try {
            service.registerObservers();
        } catch (RemoteException e) {
            PrivacyDebugger.e(TAG, "PrivacySettingsManager:registerObservers: "
                + "Exception occurred in the remote privacy service", e);
            throw new PrivacyServiceException("Exception occurred in the "
                    + "remote privacy service", e);
        }
    }

    public void addObserver(String packageName)
            throws PrivacyServiceDisconnectedException, PrivacyServiceInvalidException, 
            PrivacyServiceException {
        this.connectService();

        try {
            service.addObserver(packageName);
        } catch (RemoteException e) {
            PrivacyDebugger.e(TAG, "PrivacySettingsManager:addObserver: "
                + "Exception occurred in the remote privacy service", e);
            throw new PrivacyServiceException("Exception occurred in the "
                    + "remote privacy service", e);
        }
    }

    public boolean purgeSettings()
            throws PrivacyServiceDisconnectedException, PrivacyServiceInvalidException, 
            PrivacyServiceException {
        this.connectService();
        try {
            return service.purgeSettings();
        } catch (RemoteException e) {
            PrivacyDebugger.e(TAG, "PrivacySettingsManager:purgeSettings: 
                + "Exception occurred in the remote privacy service", e);
            throw new PrivacyServiceException("Exception occurred in the "
                    + "remote privacy service", e);
        }
    }

    @Deprecated
    public double getVersion() {
        return PrivacySettingsManagerService.API_VERSION;
    }

    public double getApiVersion() {
        return PrivacySettingsManagerService.API_VERSION;
    }

    public double getModVersion() {
        return PrivacySettingsManagerService.MOD_VERSION;
    }

    public String getModDetails() {
        return PrivacySettingsManagerService.MOD_DETAILS;
    }

    public boolean setEnabled(boolean enable)
            throws PrivacyServiceDisconnectedException, PrivacyServiceInvalidException, 
            PrivacyServiceException {
        this.connectService();

        try {
            return service.setEnabled(enable);
        } catch (RemoteException e) {
            PrivacyDebugger.e(TAG, "PrivacySettingsManager:addObserver: 
                + "Exception occurred in the remote privacy service", e);
            throw new PrivacyServiceException("Exception occurred in the "
                    + "remote privacy service", e);
        }
    }

    public boolean setNotificationsEnabled(boolean enable)
            throws PrivacyServiceDisconnectedException, PrivacyServiceInvalidException, 
            PrivacyServiceException {
        this.connectService();

        try {
            return service.setNotificationsEnabled(enable);
        } catch (RemoteException e) {
            PrivacyDebugger.e(TAG, "PrivacySettingsManager:setNotificationsEnabled: "
                + "Exception occurred in the remote privacy service", e);
            throw new PrivacyServiceException("Exception occurred in the "
                    + "remote privacy service", e);
        }
    }

    public boolean isFailSafeActive () {
       boolean output = false;
       this.connectService();
       try {
            if (isServiceAvailable()){
               output = service.isFailSafeActive();
            } else {
               PrivacyDebugger.e(TAG, "isFaileSafeActive () - PrivacySettingsManagerService is null");
            }
       } catch (RemoteException e) {
           PrivacyDebugger.e(TAG, "RemoteException in isFaileSafeActive ()", e);
       }
       return output;
    }

    /**
     * should get a call if you want to disable failSafeMode
     * TODO: rename it!
     */
    public void setFailSafeMode(boolean state) {
        this.connectService();
        try {
           if (isServiceAvailable()){
               PrivacyDebugger.i(TAG, "set now fail safe mode to:" + state);
               service.setFailSafeMode(state);
           } else {
              PrivacyDebugger.e(TAG, "ackFailSafeInformed () - PrivacySettingsManagerService is null");
           }
       } catch (RemoteException e) {
           PrivacyDebugger.e(TAG, "RemoteException in ackFailSafeInformed ()", e);
       }
    }

    public void setBootCompleted()
            throws PrivacyServiceDisconnectedException, PrivacyServiceInvalidException, 
            PrivacyServiceException {
        this.connectService();
        try {
            service.setBootCompleted();
        } catch (RemoteException e) {
            PrivacyDebugger.e(TAG, "PrivacySettingsManager:setBootCompleted: "
                + "Exception occurred in the remote privacy service", e);
            throw new PrivacyServiceException("Exception occurred in the "
                    + "remote privacy service", e);
        }
    }

    public void setDebugFlagInt(String flagName, int value)
            throws PrivacyServiceDisconnectedException, PrivacyServiceInvalidException, 
            PrivacyServiceException {
        this.connectService();

        try {
            service.setDebugFlagInt(flagName, value);
        } catch (RemoteException e) {
            PrivacyDebugger.e(TAG, "PrivacySettingsManager:setDebugFlagInt: "
                + "Exception occurred in the remote privacy service", e);
            throw new PrivacyServiceException("Exception occurred in the "
                    + "remote privacy service", e);
        }
    }

    public Integer getDebugFlagInt(String flagName)
            throws PrivacyServiceDisconnectedException, PrivacyServiceInvalidException, 
            PrivacyServiceException {
        this.connectService();

        try {
            return service.getDebugFlagInt(flagName);
        } catch (RemoteException e) {
            Privacydebugger.e(TAG, "PrivacySettingsManager:getDebugFlagInt: "
                + "Exception occurred in the remote privacy service", e);
            throw new PrivacyServiceException("Exception occurred in the "
                    + "remote privacy service", e);
        }
    }

    public void setDebugFlagBool(String flagName, boolean value) throws 
            PrivacyServiceDisconnectedException, PrivacyServiceException {
        this.connectService();

        try {
            service.setDebugFlagBool(flagName, value);
        } catch (RemoteException e) {
            PrivacyDebugger.e(TAG, "PrivacySettingsManager:setDebugFlagBool: "
                + "Exception occurred in the remote privacy service", e);
            throw new PrivacyServiceException("Exception occurred in the "
                    + "remote privacy service", e);
        }
    }

    public Boolean getDebugFlagBool(String flagName)
            throws PrivacyServiceDisconnectedException, PrivacyServiceInvalidException, 
            PrivacyServiceException {
        this.connectService();

        try {
            return service.getDebugFlagBool(flagName);
        } catch (RemoteException e) {
            PrivacyDebugger.e(TAG, "PrivacySettingsManager:getDebugFlagBoolInt: "
                + "Exception occurred in the remote privacy service", e);
            throw new PrivacyServiceException("Exception occurred in the "
                    + "remote privacy service", e);
        }
    }

    public Map<String, Integer> getDebugFlags()
            throws PrivacyServiceDisconnectedException, PrivacyServiceInvalidException, 
            PrivacyServiceException {
        this.connectService();

        try {
            return service.getDebugFlags();
        } catch (RemoteException e) {
            PrivacyDebugger.e(TAG, "PrivacySettingsManager:getDebugFlags: "
                + "Exception occurred in the remote privacy service", e);
            throw new PrivacyServiceException("Exception occurred in the "
                    + "remote privacy service", e);
        }
    }

    /**
     * Checks that the 
     * @return true if service class name matches expectations, otherwise false
     */
    private boolean isServiceValid() {
        if (!isServiceAvailable()) return false;

        String serviceClass = this.service.getClass().getCanonicalName();
        if (serviceClass.equals("android.privacy.IPrivacySettingsManager.Stub.Proxy") || 
                serviceClass.equals("android.privacy.PrivacySettingsManagerService")) {
            return true;
        } else {
            PrivacyDebugger.e(TAG, "PrivacySettingsManager:isServiceValid:"
                + "PrivacySettingsManagerService is of an incorrect class (" 
                + service.getClass().getCanonicalName() +")");
            (new Throwable()).printStackTrace();
            return false;
        }
    }

    private void isServiceValidOrThrow() throws PrivacyServiceInvalidException {
        if (!this.isServiceValid()) {
            throw new PrivacyServiceInvalidException();
        }
    }

    /**
     * Checks whether the PrivacySettingsManagerService is available. For some reason,
     * occasionally it appears to be null. In this case it should be initialized again.
     * @return true if service is connected, otherwise false
     */
    public boolean isServiceAvailable() {
        if (service == null) {
            PrivacyDebugger.e(TAG, "PrivacySettingsManager:isServiceAvailable: "
                    + "PrivacySettingsManagerService is null");
            (new Throwable()).printStackTrace();
            return false;
        } else {
            return true;
        }
    }

    /**
     * Checks whether the PrivacySettingsManagerService is available. For some reason,
     * occasionally it appears to be null. In this case it should be initialized again.
     */
    private void isServiceAvailableOrThrow() throws PrivacyServiceDisconnectedException {
        if (!this.isServiceAvailable()) {
            throw new PrivacyServiceDisconnectedException();
        }
    }

    private void connectService() throws PrivacyServiceDisconnectedException, 
            PrivacyServiceInvalidException {
        int count = 0;
        if (!isServiceAvailable() || !isServiceValid()) {
            while(!isServiceAvailable() && count < MAXIMUM_RECONNECT_COUNT) {
               reinitalizeService();
               count++;
            }
            if (this.service == null) {
                throw new PrivacyServiceDisconnectedException("Reconnection failed");
            }
        }
    }

    /**
     * reinitializes our service if it is null for some reason!
     */
    private synchronized void reinitalizeService() {
        this.service = IPrivacySettingsManager.Stub.asInterface(ServiceManager.getService("privacy"));
        PrivacyDebugger.i(TAG, "service reinitalized now!");
    }

    /**
     * Establish a connection to the Privacy service without using a Context
     * @return PrivacySettingsManager connected to the privacy service
     */
    public static PrivacySettingsManager getPrivacyService() {
        return new PrivacySettingsManager(IPrivacySettingsManager.Stub.asInterface(ServiceManager.getService("privacy"))); //we can pass null here
    }

    /**
     * Establish a connection to the Privacy service using context.getSystemService if possible, 
     * otherwise without a context
     * @param context  Context to use to connect to the service
     * @return PrivacySettingsManager connected to the privacy service
     */
    public static PrivacySettingsManager getPrivacyService(Context context) {
        try {
            if (context != null) {
                try {
                    PrivacySettingsManager privacySettingsManager = (PrivacySettingsManager) 
                            context.getSystemService("privacy");
                    privacySettingsManager.contextReference = new WeakReference<Context>(context);
                    return privacySettingsManager;
                } catch (Exception e) {
                    PrivacyDebugger.w(TAG, "PrivacySettingsManager:
                        + "getPrivacyService(Context): exception occurred trying to obtain "
                        + "static service. Falling back to non-static service.", e);
                    return getPrivacyService();
                }
            } else {
                return getPrivacyService();
            }
        } catch (Exception e) {
            PrivacyDebugger.e(TAG, "PrivacySettingsManager:getPrivacyService(Context):"
                + "exception occurred getting privacy service");
            // return a 'disconnected' privacy service manager so that it isn't null
            return new PrivacySettingsManager(null);
        }
    }
}
