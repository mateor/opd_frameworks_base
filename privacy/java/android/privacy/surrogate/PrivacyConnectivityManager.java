/**
* Copyright (C) 2012 Stefan Thiele (CollegeDev)
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

import java.net.InetAddress;

import android.content.Context;
import android.net.ConnectivityManager;
import android.net.IConnectivityManager;
import android.net.LinkProperties;
import android.net.NetworkInfo;
import android.os.Binder;
import android.os.ServiceManager;
import android.privacy.IPrivacySettingsManager;
import android.privacy.PrivacyServiceException;
import android.privacy.PrivacySettings;
import android.privacy.PrivacySettingsManager;
import android.privacy.utilities.PrivacyDebugger;
import android.util.Log;

/**
 * Provides privacy handling for phone
 * @author CollegeDev
 * @author CollegeDev (Stefan T.)
 * {@hide}
 */
public class PrivacyConnectivityManager extends ConnectivityManager{

    private static final String P_TAG = "PrivacyConnectivityManager";

    private Context context;

    private PrivacySettingsManager pSetMan;

    public PrivacyConnectivityManager(IConnectivityManager service, Context context) {
        super(service);
        this.context = context;
        pSetMan = new PrivacySettingsManager(context, 
            IPrivacySettingsManager.Stub.asInterface(ServiceManager.getService("privacy")));
        Log.i(P_TAG,"now in constructor for package: " + context.getPackageName());
    }

    @Override
    public boolean getMobileDataEnabled() {
        try {
            if (pSetMan == null) pSetMan = PrivacySettingsManager.getPrivacyService();
                PrivacySettings settings = pSetMan.getSettings(context.getPackageName());
            if(pSetMan != null && settings != null && settings.getForceOnlineState() ==
                PrivacySettings.REAL){
                    pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY,
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);  
                return true;
            }
            //      } else if(pSetMan != null && settings != null && 
            //          settings.getNetworkInfoSetting() != PrivacySettings.REAL){
            //              pSetMan.notification(context.getPackageName(),-1,
            //              PrivacySettings.EMPTY, PrivacySettings.DATA_NETWORK_INFO_CURRENT,
            //              null, null);  
            //          return false;
            //      }
            else{
                pSetMan.notification(context.getPackageName(), PrivacySettings.REAL,
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);  
                return super.getMobileDataEnabled();
            }
        } catch (PrivacyServiceException e) {
            Log.e(P_TAG, "PrivacyConnectivityManager: PrivacyServiceException occurred", e);
            pSetMan.notification(context.getPackageName(), PrivacySettings.ERROR, 
                PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);
            return true;
        }

    }

    @Override
    public void setMobileDataEnabled(boolean enabled) {
        try {
            if (pSetMan == null) pSetMan = PrivacySettingsManager.getPrivacyService();
            PrivacySettings settings = pSetMan.getSettings(context.getPackageName());
            if (settings == null || settings.getSwitchConnectivitySetting() != 
                PrivacySettings.REAL) {
                    pSetMan.notification(context.getPackageName(), PrivacySettings.REAL,
                        PrivacySettings.DATA_SWITCH_CONNECTIVITY, null);
                    super.setMobileDataEnabled(enabled);  
            } else {
                pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY, 
                    PrivacySettings.DATA_SWITCH_CONNECTIVITY, null); 
                //do nothing
            }
        } catch (PrivacyServiceException e) {
            Log.e(P_TAG, "PrivacyConnectivityManager: PrivacyServiceException occurred", e);
            pSetMan.notification(context.getPackageName(), PrivacySettings.ERROR, 
                PrivacySettings.DATA_SWITCH_CONNECTIVITY, null);
        }
    }

    @Override
    public NetworkInfo[] getAllNetworkInfo() {
        NetworkInfo output[] =  {new NetworkInfo(TYPE_MOBILE, 0, "MOBILE", "CONNECTED")};

        try {
            if (pSetMan == null) pSetMan = PrivacySettingsManager.getPrivacyService();
            PrivacySettings settings = pSetMan.getSettings(context.getPackageName());

            if (settings != null && settings.getForceOnlineState() == PrivacySettings.REAL) {
                output[0].setIsAvailable(true); 
                output[0].setState(NetworkInfo.State.CONNECTED);
                pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY, 
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);  
                return output;             
            } else if (settings == null || settings.getNetworkInfoSetting() ==
                    PrivacySettings.REAL) {
                pSetMan.notification(context.getPackageName(), PrivacySettings.REAL,
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null); 
                return super.getAllNetworkInfo();
            } else {
                pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY, 
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);  
                return output;
            }
        } catch (PrivacyServiceException e) {
            Log.e(P_TAG, "PrivacyConnectivityManager: PrivacyServiceException occurred", e);
            pSetMan.notification(context.getPackageName(), PrivacySettings.ERROR,
                PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);
            return output;
        }
    }

    @Override
    public NetworkInfo getNetworkInfo(int networkType) {
        NetworkInfo output =  new NetworkInfo(TYPE_MOBILE, 0, "MOBILE", "CONNECTED");

        try {
            if (pSetMan == null) pSetMan = PrivacySettingsManager.getPrivacyService();
            PrivacySettings settings = pSetMan.getSettings(context.getPackageName());
            if (settings != null && settings.getForceOnlineState() == PrivacySettings.REAL) {
                output.setIsAvailable(true);
                output.setState(NetworkInfo.State.CONNECTED);
                pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY,
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);  
                return output;
            } else if (settings == null || settings.getNetworkInfoSetting() ==
                PrivacySettings.REAL) {
                pSetMan.notification(context.getPackageName(), PrivacySettings.REAL,
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null); 
                return super.getNetworkInfo(networkType);
            } else {
                pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY,
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);  
                return output;
            }
        } catch (PrivacyServiceException e) {
            Log.e(P_TAG, "PrivacyConnectivityManager: PrivacyServiceException occurred", e);
            pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY,
                PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);  
            return output;        
        }

    }

    /**
     * {@hide}
     */
    @Override
    public NetworkInfo getActiveNetworkInfoForUid(int uid) {
        NetworkInfo output =  new NetworkInfo(TYPE_MOBILE, 0, "MOBILE", "UNKNOWN");
        try {
            if (pSetMan == null) pSetMan = PrivacySettingsManager.getPrivacyService();
            PrivacySettings settings = pSetMan.getSettings(context.getPackageName());
            if (settings != null && settings.getForceOnlineState() == PrivacySettings.REAL){
                output.setIsAvailable(true);
                output.setState(NetworkInfo.State.CONNECTED);
                pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY,
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);  
                return output;
            } else if (settings == null || settings.getNetworkInfoSetting() ==
                    PrivacySettings.REAL){
                pSetMan.notification(context.getPackageName(), PrivacySettings.REAL,
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null); 
                return super.getActiveNetworkInfoForUid(uid);
            } else{
                pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY, 
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);  
                return output;
            }
        } catch (PrivacyServiceException e) {
            Log.e(P_TAG, "PrivacyConnectivityManager: PrivacyServiceException occurred", e);
            pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY, 
                PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);
            return output;
        }
    }

    @Override
    public NetworkInfo getActiveNetworkInfo() {
        NetworkInfo output =  new NetworkInfo(TYPE_MOBILE, 0, "MOBILE", "UNKNOWN");

        try {
            if (pSetMan == null) pSetMan = PrivacySettingsManager.getPrivacyService();
            PrivacySettings settings = pSetMan.getSettings(context.getPackageName());
            if (settings != null && settings.getForceOnlineState() == PrivacySettings.REAL) {
                output.setIsAvailable(true);
                output.setState(NetworkInfo.State.CONNECTED);
                pSetMan.notification(context.getPackageName(), PrivacySettings.REAL,
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null); 
                return output;	            
            } else if (settings == null || settings.getNetworkInfoSetting() !=
                    PrivacySettings.REAL) {
                pSetMan.notification(context.getPackageName(), PrivacySettings.REAL,
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null); 
                return super.getActiveNetworkInfo();
            } else {
                pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY,
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);  
                return output;
            }
        } catch (PrivacyServiceException e) {
            Log.e(P_TAG, "PrivacyConnectivityManager: PrivacyServiceException occurred", e);
            pSetMan.notification(context.getPackageName(), PrivacySettings.ERROR,
                PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);
            return output;
        }
    }

    @Override
    public LinkProperties getLinkProperties(int networkType) { 
        // method to prevent getting device IP
        LinkProperties output = new LinkProperties();

        try {
            if (pSetMan == null) pSetMan = PrivacySettingsManager.getPrivacyService();
            PrivacySettings settings = pSetMan.getSettings(context.getPackageName());

            if (settings == null || settings.getNetworkInfoSetting() == 
                    PrivacySettings.REAL) {
                pSetMan.notification(context.getPackageName(), PrivacySettings.REAL,
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null); 
                return super.getLinkProperties(networkType);
            } else {
                pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY,
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);  
                return output;
            }
        } catch (PrivacyServiceException e) {
            Log.e(P_TAG, "PrivacyConnectivityManager: PrivacyServiceException occurred", e);
            pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY,
                PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);
            return output;
        }
    }

    public LinkProperties getActiveLinkProperties() { //also for prevent getting device IP
        LinkProperties output = new LinkProperties();

        try {
            if (pSetMan == null) pSetMan = PrivacySettingsManager.getPrivacyService();
            PrivacySettings settings = pSetMan.getSettings(context.getPackageName());
            if (settings == null || settings.getNetworkInfoSetting() == 
                    PrivacySettings.REAL) {
                pSetMan.notification(context.getPackageName(), PrivacySettings.REAL,
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null); 
                return super.getActiveLinkProperties();
            } else {
                pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY,
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);  
                return output;
            }
        } catch (PrivacyServiceException e) {
            Log.e(P_TAG, "PrivacyConnectivityManager: PrivacyServiceException occurred", e);
            pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY,
                PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);
            return output;
        }
    }

    @Override
    public boolean requestRouteToHost(int networkType, int hostAddress){
        try {
            if (pSetMan == null) pSetMan = PrivacySettingsManager.getPrivacyService();
            PrivacySettings settings = pSetMan.getSettings(context.getPackageName());
            if (settings != null || settings.getForceOnlineState() == PrivacySettings.REAL) {
                pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY,
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);  
                return true;
            } else if (settings == null || settings.getNetworkInfoSetting() ==
                    PrivacySettings.REAL) {
                pSetMan.notification(context.getPackageName(),-1, PrivacySettings.REAL,
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null, null); 
                return super.requestRouteToHost(networkType, hostAddress);
            } else {
                pSetMan.notification(context.getPackageName(),-1, PrivacySettings.EMPTY,
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null, null);  
                return false;
            }
        } catch (PrivacyServiceException e) {
            Log.e(P_TAG, "PrivacyConnectivityManager: PrivacyServiceException occurred", e);
            pSetMan.notification(context.getPackageName(), PrivacySettings.ERROR,
                PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);
            return true;
        }
    }

    @Override
    public boolean requestRouteToHostAddress(int networkType, InetAddress hostAddress){

        try {
            if (pSetMan == null) pSetMan = PrivacySettingsManager.getPrivacyService();
            PrivacySettings settings = pSetMan.getSettings(context.getPackageName());
            if (settings != null && settings.getForceOnlineState() == PrivacySettings.REAL) {
                pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY,
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);  
                return true;
            } else if (settings == null || settings.getNetworkInfoSetting() ==
                    PrivacySettings.REAL){
                pSetMan.notification(context.getPackageName(), PrivacySettings.REAL,
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null); 
                return super.requestRouteToHostAddress(networkType, hostAddress);
            } else{
                pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY,
                    PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);  
                return false;
        }
        } catch (PrivacyServiceException e) {
            Log.e(P_TAG, "PrivacyConnectivityManager: PrivacyServiceException occurred", e);
            pSetMan.notification(context.getPackageName(), PrivacySettings.ERROR,
                PrivacySettings.DATA_NETWORK_INFO_CURRENT, null);
            return true;
        }
    }
}
