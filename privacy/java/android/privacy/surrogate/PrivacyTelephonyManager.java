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

import com.android.internal.telephony.IPhoneStateListener;

import android.content.Context;
import android.os.Binder;
import android.os.Bundle;
import android.os.Handler;
import android.os.Message;
import android.os.RemoteException;
import android.os.ServiceManager;
import android.privacy.IPrivacySettingsManager;
import android.privacy.PrivacyServiceException;
import android.privacy.PrivacySettings;
import android.privacy.PrivacySettingsManager;
import android.privacy.utilities.PrivacyDebugger;
import android.telephony.CellLocation;
import android.telephony.NeighboringCellInfo;
import android.telephony.PhoneStateListener;
import android.telephony.ServiceState;
import android.telephony.SignalStrength;
import android.telephony.TelephonyManager;
import android.util.Log;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Random;

import android.telephony.CellInfo;

/**
 * Provides privacy handling for {@link android.telephony.TelephonyManager}
 * @author Svyatoslav Hresyk
 * {@hide}
 */
public final class PrivacyTelephonyManager extends TelephonyManager {

    private static final String TAG = "PrivacyTelephonyManager";

    private Context context;

    private PrivacySettingsManager pSetMan;

    /** {@hide} */
    public PrivacyTelephonyManager(Context context) {
        super(context);
        this.context = context;

        // don't call getSystemService to avoid getting java.lang.IllegalStateException: 
        // System services not available to Activities before onCreate()
        pSetMan = PrivacySettingsManager.getPrivacyService();
    }

    /**
     * IMEI
     */
    @Override
    public String getDeviceId() {
        String packageName = context.getPackageName();
        String output;
        try {
            PrivacySettings pSet = pSetMan.getSettings(packageName);
            if (pSet == null || pSet.getDeviceIdSetting() == PrivacySettings.REAL) {
                output = super.getDeviceId();
                pSetMan.notification(packageName, PrivacySettings.REAL,
                    PrivacySettings.DATA_DEVICE_ID, output);
            } else {
                output = pSet.getDeviceId(); // can be empty, custom or random
                pSetMan.notification(packageName, pSet.getDeviceIdSetting(),
                    PrivacySettings.DATA_DEVICE_ID, output);
            }
        } catch (PrivacyServiceException e) {
            output = "";
            pSetMan.notification(packageName, PrivacySettings.ERROR,
                PrivacySettings.DATA_DEVICE_ID, output);
        } catch (NullPointerException e) {
            PrivacyDebugger.e(TAG, "PrivacyTelphonyManager:NullPointerException: "
                + "probably privacy service", e);
            output = "";
        }
        return output;
    }

    /**
     * Phone number
     */
    @Override
    public String getLine1Number() {
        String packageName = context.getPackageName();
        String output;
        try {
            PrivacySettings pSet = pSetMan.getSettings(packageName);
            if (pSet == null || pSet.getLine1NumberSetting() == PrivacySettings.REAL) {
                output = super.getLine1Number();
                pSetMan.notification(packageName, PrivacySettings.REAL, 
                    PrivacySettings.DATA_LINE_1_NUMBER, output);
            } else {
                output = pSet.getLine1Number(); // can be empty, custom or random
                pSetMan.notification(packageName, pSet.getLine1NumberSetting(), 
                    PrivacySettings.DATA_LINE_1_NUMBER, output);
            }
        } catch (PrivacyServiceException e) {
            output = "";
            pSetMan.notification(packageName, PrivacySettings.ERROR, 
                PrivacySettings.DATA_LINE_1_NUMBER, output);
        } catch (NullPointerException e) {
            PrivacyDebugger.e(TAG, "PrivacyTelphonyManager:NullPointerException: "
                + "probably privacy service", e);
            output = "";
        }
        return output;
    }

    /**
     * Will be handled like the Line1Number, since voice mailbox numbers often
     * are similar to the phone number of the subscriber.
     */
    @Override
    public String getVoiceMailNumber() {
        String packageName = context.getPackageName();
        String output;
        try {
            PrivacySettings pSet = pSetMan.getSettings(packageName);
            if (pSet == null || pSet.getLine1NumberSetting() == PrivacySettings.REAL) {
                output = super.getVoiceMailNumber();
                pSetMan.notification(packageName, PrivacySettings.REAL, 
                    PrivacySettings.DATA_LINE_1_NUMBER, output);
            } else {
                output = pSet.getLine1Number(); // can be empty, custom or random
                pSetMan.notification(packageName, pSet.getLine1NumberSetting(), 
                    PrivacySettings.DATA_LINE_1_NUMBER, output);
            }
        } catch (PrivacyServiceException e) {
            output = "";
            pSetMan.notification(packageName, PrivacySettings.ERROR, 
                PrivacySettings.DATA_LINE_1_NUMBER, output);
        } catch (NullPointerException e) {
            PrivacyDebugger.e(TAG, "PrivacyTelphonyManager:NullPointerException: "
                + "probably privacy service", e);
            output = "";
        }
        return output;
    }

    /**
     * Intercept requests for mobile network cell information. 
     * This can be used for tracking network
     * based location.
     */
    @Override
    public List<NeighboringCellInfo> getNeighboringCellInfo() {
        // **SM: don't need some kind of notification for this?
        List<NeighboringCellInfo> output = null;
        String output_label = "[null]";
        try {
            PrivacySettings pSet = pSetMan.getSettings(context.getPackageName());
            if (pSet == null || pSet.getLocationNetworkSetting() ==  PrivacySettings.REAL) {
                output = super.getNeighboringCellInfo();
                String cells = "";
                for (NeighboringCellInfo i : output) cells += "\t" + i + "\n";
                output_label = "[real value]:\n" + cells;
            } else if (pSet.getLocationNetworkSetting() == PrivacySettings.EMPTY) {
                // output = null;
            } else {
                output = new ArrayList<NeighboringCellInfo>();
                output_label = "[empty list of cells]";
            }
        } catch (PrivacyServiceException e) {
        } catch (NullPointerException e) {
            PrivacyDebugger.e(TAG, "PrivacyTelphonyManager:NullPointerException: "
                + "probably privacy service", e);
        }
        return output;
    }

    @Override
    public String getNetworkCountryIso() {
        String output = getNetworkInfo();
        if (output == null) output = super.getNetworkCountryIso();
        //  PrivacyDebugger.d(TAG, "getNetworkCountryIso - " + context.getPackageName() 
        //      + " (" + Binder.getCallingUid() + ") output: " + output);
        return output;
    }

    @Override
    public String getNetworkOperator() {
        String output = getNetworkInfo();
        if (output == null) output = super.getNetworkOperator();
        //  PrivacyDebugger.d(TAG, "getNetworkOperator - " + context.getPackageName()
        //      + " (" + Binder.getCallingUid() + ") output: " + output);
        return output;
    }

    @Override
    public String getNetworkOperatorName() {
        String output = getNetworkInfo();
        if (output == null) output = super.getNetworkOperatorName();
        //  PrivacyDebugger.d(TAG, "getNetworkOperatorName - " + context.getPackageName() 
        //      + " (" + Binder.getCallingUid() + ") output: " + output);
        return output;
    }

    /**
     * Handles following Network Information requests: CountryIso, Operator Code, 
     *      Operator Name
     * @return value to return if applicable or null if real value should be returned
     */
    private String getNetworkInfo() {
        String packageName = context.getPackageName();
        try {
            PrivacySettings pSet = pSetMan.getSettings(packageName);
            if (pSet == null || pSet.getNetworkInfoSetting() == PrivacySettings.REAL) {
                pSetMan.notification(packageName, PrivacySettings.REAL, 
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);            
                return null;
            } else {
                pSetMan.notification(packageName, PrivacySettings.EMPTY, 
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);            
                return ""; // can only be empty
            }
        } catch (PrivacyServiceException e) {
            pSetMan.notification(packageName, PrivacySettings.ERROR, 
                PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);            
            return ""; // can only be empty            
        } catch (NullPointerException e) {
            PrivacyDebugger.e(TAG, "PrivacyTelphonyManager:NullPointerException: "
                + "probably privacy service", e);
            return "";
        }
    }

    @Override
    public String getSimCountryIso() {
        String output = getSimInfo();
        if (output == null) output = super.getSimCountryIso();
        //  PrivacyDebugger.d(TAG, "getSimCountryIso - " + context.getPackageName() 
        //      + " (" + Binder.getCallingUid() + ") output: " + output);
        return output;
    }

    @Override
    public String getSimOperator() {
        String output = getSimInfo();
        if (output == null) output = super.getSimOperator();
        //  PrivacyDebugger.d(TAG, "getSimOperator - " + context.getPackageName()
        //      + " (" + Binder.getCallingUid() + ") output: " + output);
        return output;
    }

    @Override
    public String getSimOperatorName() {
        String output = getSimInfo();
        if (output == null) output = super.getSimOperatorName();
        //  PrivacyDebugger.d(TAG, "getSimOperatorName - " + context.getPackageName() 
        //      + " (" + Binder.getCallingUid() + ") output: " + output);
        return output;
    }

    /**
     * Handles following SIM Card information requests: CountryIso, Operator Code,
     *      Operator Name
     * @return value to return if applicable or null if real value should be returned
     */
    private String getSimInfo() {
        String packageName = context.getPackageName();
        try {
            PrivacySettings pSet = pSetMan.getSettings(packageName);
            if (pSet != null && pSet.getSimInfoSetting() != PrivacySettings.REAL) {
                pSetMan.notification(packageName, PrivacySettings.EMPTY, 
                    PrivacySettings.DATA_NETWORK_INFO_SIM, null);
                return ""; // can only be empty
            } else {
                pSetMan.notification(packageName, PrivacySettings.REAL, 
                    PrivacySettings.DATA_NETWORK_INFO_SIM, null);
                return null;
            }
        } catch (PrivacyServiceException e) {
            pSetMan.notification(packageName, PrivacySettings.ERROR, 
                PrivacySettings.DATA_NETWORK_INFO_SIM, null);
            return ""; // can only be empty
        } catch (NullPointerException e) {
            PrivacyDebugger.e(TAG, "PrivacyTelphonyManager:NullPointerException: "
                + "probably privacy service", e);
            return "";
        }
    }

    /**
     * ICCID
     */
    @Override
    public String getSimSerialNumber() {
        String packageName = context.getPackageName();
        String output;
        try {
            PrivacySettings pSet = pSetMan.getSettings(packageName);
            if (pSet == null || pSet.getSimSerialNumberSetting() == PrivacySettings.REAL) {
                output = super.getSimSerialNumber();
                pSetMan.notification(packageName, PrivacySettings.REAL, 
                    PrivacySettings.DATA_SIM_SERIAL, output);
            } else {
                output = pSet.getSimSerialNumber(); // can be empty, custom or random
                pSetMan.notification(packageName, pSet.getSimSerialNumberSetting(), 
                    PrivacySettings.DATA_SIM_SERIAL, output);            
            }
        } catch (PrivacyServiceException e) {
            output = "";
            pSetMan.notification(packageName, PrivacySettings.ERROR, 
                PrivacySettings.DATA_SIM_SERIAL, output);            
        } catch (NullPointerException e) {
            PrivacyDebugger.e(TAG, "PrivacyTelphonyManager:NullPointerException: "
                + "probably privacy service", e);
            output = "";
        }

        return output;
    }

    /**
     * IMSI
     */
    @Override
    public String getSubscriberId() {
        String packageName = context.getPackageName();
        String output;
        try {
            PrivacySettings pSet = pSetMan.getSettings(packageName);
            if (pSet == null || pSet.getSubscriberIdSetting() == PrivacySettings.REAL) {
                output = super.getSubscriberId();
                pSetMan.notification(packageName, PrivacySettings.REAL, 
                    PrivacySettings.DATA_SUBSCRIBER_ID, output);
            } else {
                output = pSet.getSubscriberId(); // can be empty, custom or random
                pSetMan.notification(packageName, pSet.getSubscriberIdSetting(), 
                    PrivacySettings.DATA_SUBSCRIBER_ID, output);            
            }
        } catch (PrivacyServiceException e) {
            output = "";
            pSetMan.notification(packageName, PrivacySettings.ERROR, 
                PrivacySettings.DATA_SUBSCRIBER_ID, output);            
        } catch (NullPointerException e) {
            PrivacyDebugger.e(TAG, "PrivacyTelphonyManager:NullPointerException: "
                + "probably privacy service", e);
            output = "";
        }
        return output;
    }

    /**
     * For monitoring purposes only
     */    
    //    @Override
    //    public void enableLocationUpdates() {
    //        PrivacyDebugger.d(TAG, "enableLocationUpdates - " + context.getPackageName() 
    //            + " (" + Binder.getCallingUid() + ")");
    //        super.enableLocationUpdates();
    //    }

    @Override
    public void listen(PhoneStateListener listener, int events) {
        //  PrivacyDebugger.d(TAG, "listen - package:" + context.getPackageName() + " uid:"
        //      + Binder.getCallingUid() + " events: " + events);
        if (((events & PhoneStateListener.LISTEN_CELL_LOCATION) != 0) || ((events & PhoneStateListener.LISTEN_CALL_STATE) != 0)) {
            //  first check if context exists
            String pkgForDebug = context != null ? context.getPackageName() : null;
            if(pkgForDebug != null){
                listener.setPackageName(pkgForDebug); 
                //  we only have to set it if context != null, because if context == null 
                //  will cause the listener gives no update to app
                listener.setContext(context);
            }
            listener.setUid(Binder.getCallingUid());
            super.listen(listener, events);
            //  PrivacyDebugger.d(TAG, "listen for cell location or call state - " 
            //      + context.getPackageName() + " (" + 
            //  Binder.getCallingUid() + ") output: custom listener");
        } else {
            super.listen(listener, events);
        }
    }

    /**
     * Returns the current location of the device.
     * Return null if current location is not available.
     * That method is new -> fix it!
     * @author CollegeDev
     */
    @Override
    public CellLocation getCellLocation() {
        String packageName = context.getPackageName();
        try {
            PrivacySettings pSet = pSetMan.getSettings(packageName);
            if (pSet == null || pSet.getLocationNetworkSetting() == PrivacySettings.REAL) {
                pSetMan.notification(packageName, pSet.getLocationNetworkSetting(), 
                    PrivacySettings.DATA_LOCATION_NETWORK, null);
                CellLocation cl = super.getCellLocation();
                return cl;
            } else {
                pSetMan.notification(packageName, pSet.getLocationNetworkSetting(), 
                    PrivacySettings.DATA_LOCATION_NETWORK, null);
                return null;
            }
        } catch (PrivacyServiceException e) {
            pSetMan.notification(packageName, PrivacySettings.ERROR, 
                PrivacySettings.DATA_LOCATION_NETWORK, null);
            return null;
        } catch (NullPointerException e) {
            PrivacyDebugger.e(TAG, "PrivacyTelphonyManager:NullPointerException: "
                + "probably privacy service", e);
            return null;
        }
    }

    /**
     * Returns the software version number for the device, for example,
     * the IMEI/SV for GSM phones. Can control with deviceIdSetting
     *
     */
    @Override
    public String getDeviceSoftwareVersion() {
        String packageName = context.getPackageName();
        String output = "";
        try {
            PrivacySettings pSet = pSetMan.getSettings(packageName);
            if (pSet == null || pSet.getDeviceIdSetting() == PrivacySettings.REAL) {
                output = super.getDeviceSoftwareVersion();
                pSetMan.notification(packageName, PrivacySettings.REAL, 
                    PrivacySettings.DATA_DEVICE_ID, output);
            } else {
                output = pSet.getDeviceId(); // can be empty, custom or random
                pSetMan.notification(packageName, pSet.getDeviceIdSetting(), 
                    PrivacySettings.DATA_DEVICE_ID, output);
            }
        } catch (PrivacyServiceException e){
            pSetMan.notification(packageName, PrivacySettings.ERROR, 
                PrivacySettings.DATA_DEVICE_ID, output);
        } catch (NullPointerException e) {
            PrivacyDebugger.e(TAG, "PrivacyTelphonyManager:NullPointerException: "
                + "probably privacy service", e);
        }
        return output;
    }

    /**
     * 
     * @hide
     */
    @Override
    public String getCompleteVoiceMailNumber() {
        String packageName = context.getPackageName();
        String output = "";
        try {
            PrivacySettings pSet = pSetMan.getSettings(packageName);
            if (pSet != null && pSet.getLine1NumberSetting() != PrivacySettings.REAL) {
                output = pSet.getLine1Number(); // can be empty, custom or random
                pSetMan.notification(packageName, pSet.getLine1NumberSetting(),
                    PrivacySettings.DATA_LINE_1_NUMBER, output);
            } else {
                output = super.getCompleteVoiceMailNumber();
                pSetMan.notification(packageName, PrivacySettings.REAL, 
                    PrivacySettings.DATA_LINE_1_NUMBER, output);
            }
        } catch (PrivacyServiceException e){
            output = null;
            pSetMan.notification(packageName, PrivacySettings.ERROR, 
                PrivacySettings.DATA_LINE_1_NUMBER, output);
        } catch (NullPointerException e) {
            PrivacyDebugger.e(TAG, "PrivacyTelphonyManager:NullPointerException: "
                + "probably privacy service", e);
            output = null;
        } catch (Exception e) {
            PrivacyDebugger.e(TAG, "PrivacyTelphonyManager:Exception occurred", e);
            output = null;
        }

        return output;
    }
    //all types for better overview, based on ics 4.0.4
    private static final int PHONE_TYPES[] = {
        PHONE_TYPE_NONE, PHONE_TYPE_GSM, PHONE_TYPE_CDMA, PHONE_TYPE_SIP};
    private static final int NETWORK_TYPES[] = {
        NETWORK_TYPE_UNKNOWN, NETWORK_TYPE_GPRS, NETWORK_TYPE_EDGE,
        NETWORK_TYPE_UMTS, NETWORK_TYPE_CDMA, NETWORK_TYPE_EVDO_0,
        NETWORK_TYPE_EVDO_A, NETWORK_TYPE_1xRTT, NETWORK_TYPE_HSDPA,
        NETWORK_TYPE_HSUPA, NETWORK_TYPE_HSPA, NETWORK_TYPE_IDEN,
        NETWORK_TYPE_EVDO_B, NETWORK_TYPE_LTE, NETWORK_TYPE_EHRPD,
        NETWORK_TYPE_HSPAP};

    /**
     * Returns a constant indicating the device phone type. 
     * If user block network info, it returns random generated type of phone.
     *
     * @see #PHONE_TYPE_NONE
     * @see #PHONE_TYPE_GSM
     * @see #PHONE_TYPE_CDMA
     * @see #PHONE_TYPE_SIP
     */
    @Override
    public int getPhoneType() {
        String output = getNetworkInfo();
        //  no random support until now in pdroid, change addonApp to support it?
        //  Random x = new Random();
        int type = PHONE_TYPES[/*x.nextInt(PHONE_TYPES.length-1)*/0];
        if(output == null) type = super.getPhoneType();
        return type;
    }

    /**
     * Returns a constant indicating the radio technology (network type)
     * currently in use on the device for data transmission.
     * (If user block network info, it returns random generated type of network.)
     * @return the network type
     *
     * @see #NETWORK_TYPE_UNKNOWN
     * @see #NETWORK_TYPE_GPRS
     * @see #NETWORK_TYPE_EDGE
     * @see #NETWORK_TYPE_UMTS
     * @see #NETWORK_TYPE_HSDPA
     * @see #NETWORK_TYPE_HSUPA
     * @see #NETWORK_TYPE_HSPA
     * @see #NETWORK_TYPE_CDMA
     * @see #NETWORK_TYPE_EVDO_0
     * @see #NETWORK_TYPE_EVDO_A
     * @see #NETWORK_TYPE_EVDO_B
     * @see #NETWORK_TYPE_1xRTT
     * @see #NETWORK_TYPE_IDEN
     * @see #NETWORK_TYPE_LTE
     * @see #NETWORK_TYPE_EHRPD
     * @see #NETWORK_TYPE_HSPAP
     */
    @Override
    public int getNetworkType() {
        try{
            String output = getNetworkInfo();
            //no random support until now in pdroid, change addonApp to support it?
            //Random x = new Random();
            int type = NETWORK_TYPES[/*x.nextInt(NETWORK_TYPES.length-1)*/0];
            if(output == null) type = super.getNetworkType();
            return type;

        } catch(Exception e){
            return NETWORK_TYPES[0];
        }
    }

    /**
     * Will be handled like getLine1Number
     */
    @Override
    public String getLine1AlphaTag(){
        return getLine1Number();
    }

    /**
     * 15 character long numbers -> handle same as imsi
     */
    public String getMsisdn() {
        PrivacyDebugger.i(TAG, "getMsisdn() - " + context.getPackageName());
        return getSubscriberId();
    }

    /**
     * It doesn't matter if we give some shit to it, it will work
     */
    public String getVoiceMailAlphaTag() {
        return getVoiceMailNumber();
    }

    /**
     * @hide
     * handles like subscriber id
     */
    public String getIsimImpi() {
        PrivacyDebugger.i(TAG, "getIsimImpi - " + context.getPackageName());
        return getSubscriberId();
    }

    /**
     * @hide
     * lets play with this function, handled like NetworkOperatorName
     */
    public String getIsimDomain() {
        return getNetworkOperatorName();
    }

    /**
     * @hide
     * lets play with this function, handled like subscriberID
     */
    public String[] getIsimImpu() {
        String packageName = context.getPackageName();
        String output[] = new String[1];
        try {
            PrivacySettings pSet = pSetMan.getSettings(packageName);
            if (pSet == null || pSet.getSubscriberIdSetting() == PrivacySettings.REAL) {
                output = super.getIsimImpu();
                pSetMan.notification(packageName, PrivacySettings.REAL, 
                    PrivacySettings.DATA_SUBSCRIBER_ID, output[0]);
            } else {
                output[0] = pSet.getSubscriberId(); // can be empty, custom or random
                pSetMan.notification(packageName, pSet.getSubscriberIdSetting(), 
                    PrivacySettings.DATA_SUBSCRIBER_ID, output[0]);            
            }
        } catch (PrivacyServiceException e) {
            output[0] = "";
            pSetMan.notification(packageName, PrivacySettings.ERROR, 
                PrivacySettings.DATA_SUBSCRIBER_ID, output[0]);            
        } catch (NullPointerException e) {
            PrivacyDebugger.e(TAG, "PrivacyTelphonyManager:NullPointerException: "
                + "probably privacy service", e);
            output[0] = "";
        }
        return output;
    }
    /**
     * @hide
     * @return
     * **SM: Should be a notification here?
     */
    public List<CellInfo> getAllCellInfo() {
        List<CellInfo> output = null;
        try {
            PrivacySettings pSet = pSetMan.getSettings(context.getPackageName());
            if (pSet == null || pSet.getLocationNetworkSetting() == PrivacySettings.REAL) {
                output = super.getAllCellInfo();
            } else {
                output = new ArrayList<CellInfo>();
            }
        } catch (PrivacyServiceException e) {
            output = new ArrayList<CellInfo>();
        } catch (NullPointerException e) {
            PrivacyDebugger.e(TAG, "PrivacyTelphonyManager:NullPointerException: "
                + "probably privacy service", e);
            output = new ArrayList<CellInfo>();
        }
        return output;
    }
}
