/**
 * Copyright (C) 2012 Stefan Thiele
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

import java.util.ArrayList;
import java.util.List;

import android.content.Context;
import android.net.DhcpInfo;
import android.net.wifi.IWifiManager;
import android.net.wifi.ScanResult;
import android.net.wifi.WifiConfiguration;
import android.net.wifi.WifiInfo;
import android.net.wifi.WifiManager;
import android.os.Binder;
import android.os.ServiceManager;
import android.privacy.IPrivacySettingsManager;
import android.privacy.PrivacyServiceException;
import android.privacy.PrivacySettings;
import android.privacy.PrivacySettingsManager;
import android.util.Log;

/**
 * Provides privacy handling for WifiManager
 * @author CollegeDev
 * {@hide}
 */
public class PrivacyWifiManager extends WifiManager{

    private Context context;
    private PrivacySettingsManager pSetMan;
    private static final String P_TAG = "PrivacyWifiManager";

    private enum PrivacyOutcome { REAL, EMPTY, CUSTOM, RANDOM, ERROR, FORCE_ONLINE };

    public PrivacyWifiManager(Context context, IWifiManager service){
        super(context, service);
        this.context = context;
        pSetMan = PrivacySettingsManager.getPrivacyService();
    }

    private PrivacyOutcome getPrivacyOutcome(boolean withForceState) {
        try {
            if (pSetMan == null) pSetMan = PrivacySettingsManager.getPrivacyService();
            PrivacySettings settings = pSetMan.getSettings(context.getPackageName());
            if (withForceState && settings != null && settings.getForceOnlineState() == 
                PrivacySettings.REAL) {
                return PrivacyOutcome.FORCE_ONLINE;
            } else if (settings == null) {
                return PrivacyOutcome.REAL;
            } else {
                switch (settings.getWifiInfoSetting()) {
                case PrivacySettings.REAL:
                    return PrivacyOutcome.REAL;
                case PrivacySettings.EMPTY:
                    return PrivacyOutcome.EMPTY;
                case PrivacySettings.CUSTOM:
                    return PrivacyOutcome.CUSTOM;
                case PrivacySettings.RANDOM:
                    return PrivacyOutcome.RANDOM;
                default:
                    return PrivacyOutcome.ERROR;
                }
            }
        } catch (PrivacyServiceException e) {
            return PrivacyOutcome.ERROR;
        }
    }

    @Override
    public List<WifiConfiguration> getConfiguredNetworks() {
        switch (getPrivacyOutcome(false)) {
        case REAL:
            pSetMan.notification(context.getPackageName(), PrivacySettings.REAL, 
                PrivacySettings.DATA_WIFI_INFO, null); 
            return super.getConfiguredNetworks();
        case ERROR:
            if (pSetMan != null) {
                pSetMan.notification(context.getPackageName(), PrivacySettings.ERROR, 
                    PrivacySettings.DATA_WIFI_INFO, null);
            }
            return new ArrayList<WifiConfiguration>(); //create empty list!
        default:
            pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY, 
                PrivacySettings.DATA_WIFI_INFO, null);
            return new ArrayList<WifiConfiguration>(); //create empty list!
        }
    }

    @Override
    public WifiInfo getConnectionInfo() {
        switch (getPrivacyOutcome(false)) {
        case REAL:
            pSetMan.notification(context.getPackageName(), PrivacySettings.REAL, 
                PrivacySettings.DATA_WIFI_INFO, null); 
            return super.getConnectionInfo();
        case ERROR:
            if (pSetMan != null) {
                pSetMan.notification(context.getPackageName(), PrivacySettings.ERROR, 
                    PrivacySettings.DATA_WIFI_INFO, null);
            }
            return new WifiInfo(true);
        default:
            pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY, 
                PrivacySettings.DATA_WIFI_INFO, null);  
            return new WifiInfo(true);
        }
    }

    @Override
    public List<ScanResult> getScanResults() {
        switch (getPrivacyOutcome(false)) {
        case REAL:
            pSetMan.notification(context.getPackageName(), PrivacySettings.REAL, 
                PrivacySettings.DATA_WIFI_INFO, null); 
            return super.getScanResults();
        case ERROR:
            if (pSetMan != null) {
                pSetMan.notification(context.getPackageName(), PrivacySettings.ERROR, 
                    PrivacySettings.DATA_WIFI_INFO, null);
            }
            return new ArrayList<ScanResult>(); //create empty list!
        default:
            pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY, 
                PrivacySettings.DATA_WIFI_INFO, null);  
            return new ArrayList<ScanResult>(); //create empty list!
        }
    }

    @Override
    public int getFrequencyBand() {
        switch (getPrivacyOutcome(false)) {
        case REAL:
            pSetMan.notification(context.getPackageName(), PrivacySettings.REAL, 
                PrivacySettings.DATA_WIFI_INFO, null); 
            return super.getFrequencyBand();
        case ERROR:
            if (pSetMan != null) {
                pSetMan.notification(context.getPackageName(), PrivacySettings.ERROR, 
                    PrivacySettings.DATA_WIFI_INFO, null);
            }
            return -1;
        default:
            pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY, PrivacySettings.DATA_WIFI_INFO, null);  
            return -1;
        }
    }

    @Override
    public DhcpInfo getDhcpInfo() {
        switch (getPrivacyOutcome(false)) {
        case REAL:
            pSetMan.notification(context.getPackageName(), PrivacySettings.REAL, 
                PrivacySettings.DATA_WIFI_INFO, null); 
            return super.getDhcpInfo();

        case ERROR:
            if (pSetMan != null) {
                pSetMan.notification(context.getPackageName(), PrivacySettings.ERROR, 
                    PrivacySettings.DATA_WIFI_INFO, null);
            }
            return new DhcpInfo();

        default:
            pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY, 
                PrivacySettings.DATA_WIFI_INFO, null);  
            return new DhcpInfo();
        }
    }

    /**
     * @hide
     * @return
     */
     @Override
     public WifiConfiguration getWifiApConfiguration() {
         switch (getPrivacyOutcome(false)) {
         case REAL:
             pSetMan.notification(context.getPackageName(), PrivacySettings.REAL, 
                PrivacySettings.DATA_WIFI_INFO, null); 
             return super.getWifiApConfiguration();
         case ERROR:
             if (pSetMan != null) {
                 pSetMan.notification(context.getPackageName(), PrivacySettings.ERROR, 
                    PrivacySettings.DATA_WIFI_INFO, null);
             }
             return new WifiConfiguration(); 
         default:
             pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY, 
                PrivacySettings.DATA_WIFI_INFO, null);  
             return new WifiConfiguration();
         }
     }


     @Override
     public String getConfigFile() {
         switch (getPrivacyOutcome(false)) {
         case REAL:
             pSetMan.notification(context.getPackageName(), PrivacySettings.REAL, 
                PrivacySettings.DATA_WIFI_INFO, null); 
             return super.getConfigFile();
         case ERROR:
             if (pSetMan != null) {
                 pSetMan.notification(context.getPackageName(), PrivacySettings.ERROR, 
                    PrivacySettings.DATA_WIFI_INFO, null);
             }
             return "";
         default:
             pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY, 
                PrivacySettings.DATA_WIFI_INFO, null);  
             return "";
         }
     }


     //new
     @Override
     public boolean startScan(){
         switch (getPrivacyOutcome(false)) {
         case REAL:
             pSetMan.notification(context.getPackageName(), PrivacySettings.REAL, 
                PrivacySettings.DATA_WIFI_INFO, null); 
             return super.startScan();
         case ERROR:
             if (pSetMan != null) {
                 pSetMan.notification(context.getPackageName(), PrivacySettings.ERROR, 
                    PrivacySettings.DATA_WIFI_INFO, null);
             }
             return false;
         default:
             pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY, 
                PrivacySettings.DATA_WIFI_INFO, null);  
             return false;
         }
     }

     @Override
     public boolean startScanActive(){
         switch (getPrivacyOutcome(false)) {
         case REAL:
             pSetMan.notification(context.getPackageName(), PrivacySettings.REAL, 
                PrivacySettings.DATA_WIFI_INFO, null); 
             return super.startScanActive();
         case ERROR:
             if (pSetMan != null) {
                 pSetMan.notification(context.getPackageName(), PrivacySettings.ERROR, 
                    PrivacySettings.DATA_WIFI_INFO, null);
             }
             return false;
         default:
             pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY, 
                PrivacySettings.DATA_WIFI_INFO, null);  
             return false;
         }
     }


     @Override
     public boolean setWifiEnabled(boolean enabled){
         switch (getPrivacyOutcome(false)) {
         case REAL:
             pSetMan.notification(context.getPackageName(), PrivacySettings.REAL, 
                PrivacySettings.DATA_SWITCH_WIFI_STATE, null); 
             return super.setWifiEnabled(enabled);
         case ERROR:
             if (pSetMan != null) {
                 pSetMan.notification(context.getPackageName(), PrivacySettings.ERROR, 
                    PrivacySettings.DATA_SWITCH_WIFI_STATE, null);
             }
             return false;
         default:
             pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY, 
                PrivacySettings.DATA_SWITCH_WIFI_STATE, null);  
             return false;		        
         }
     }

     @Override
     public int getWifiState(){
         switch (getPrivacyOutcome(true)) {
         case FORCE_ONLINE:
             pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY, 
                PrivacySettings.DATA_WIFI_INFO, null);  
             return WIFI_STATE_ENABLED;
         case REAL:
             pSetMan.notification(context.getPackageName(), PrivacySettings.REAL, 
                PrivacySettings.DATA_WIFI_INFO, null);  
             return super.getWifiState();
         case ERROR:
             if (pSetMan != null) {
                 pSetMan.notification(context.getPackageName(), PrivacySettings.ERROR, 
                    PrivacySettings.DATA_WIFI_INFO, null);
             }
             return WIFI_STATE_UNKNOWN;
         default:
             pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY, 
                PrivacySettings.DATA_WIFI_INFO, null);  
             return WIFI_STATE_UNKNOWN;
         }
     }

     @Override
     public boolean isWifiEnabled(){
         switch (getPrivacyOutcome(true)) {
         case FORCE_ONLINE:
             pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY, 
                PrivacySettings.DATA_WIFI_INFO, null);  
             return true;	            
         case REAL:
             pSetMan.notification(context.getPackageName(), PrivacySettings.REAL, 
                PrivacySettings.DATA_WIFI_INFO, null);  
             return super.isWifiEnabled();
         case ERROR:
             if (pSetMan != null) {
                 pSetMan.notification(context.getPackageName(), PrivacySettings.ERROR, 
                    PrivacySettings.DATA_WIFI_INFO, null);
             }
             return false;
         default:
             pSetMan.notification(context.getPackageName(), PrivacySettings.EMPTY, 
                PrivacySettings.DATA_WIFI_INFO, null);  
             return false;
         }
     }

}
