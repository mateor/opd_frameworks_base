package android.privacy;

import java.util.ArrayList;
import java.util.HashMap;

import android.privacy.PrivacySettings;
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
/**
 * {@hide}
 *
 */
public final class PrivacyCache {

    private static final String TAG = "PrivacyCache";

    /**
     * Cache holds all fresh settings -> speeds up accesses and saves battery consumption
     */
    private final HashMap<String, PrivacySettings> mCache = new HashMap<String, PrivacySettings>();
    
    /**
     * Checks whether the settings are available in cache or not.
     * @param packageName the packageName of the application
     * @return	true if cache contains settings for packageName, false otherwise
     */
    public boolean containsSetting(String packageName) {
        if(packageName == null){
            PrivacyDebugger.e(TAG,"passed null to containsSetting, return false");
            return false;
        }
        boolean output = false;
        synchronized(mCache) {
            output = mCache.containsKey(packageName);
        }
        return output;
    }

    /**
     * 
     * @param packageName the packageName of the application
     * @return the privacySettings for the given applicationName or null if cache doesn't contain this setting
     */
    public PrivacySettings getSettings(String packageName) {
        if(packageName == null) {
            PrivacyDebugger.e(TAG,"passed null to getSettings(), return");
            return null;
        }
        PrivacySettings output = null;
        synchronized(mCache) {
            output = mCache.get(packageName);
            PrivacyDebugger.i(TAG, "cache contains package: " + packageName + " -> " + output);
        }
        return output;
    }

    /**
     * Fills the cache with given DataSet. Data which exists will be overwritten
     * @param dataSet collections of privacySettings you want to store in cache
     */
    public void fillCache(ArrayList<PrivacySettings> dataSet) {
        if(dataSet.isEmpty() || dataSet == null) {
            PrivacyDebugger.e(TAG,"can't fill cache, because list is empty or null!");
        }
        synchronized(mCache) {
            for(PrivacySettings settings : dataSet) {
                mCache.put(settings.getPackageName(), settings);
                PrivacyDebugger.i(TAG,"put package: " + settings.getPackageName() +" to cache");
            }
        }

    }

    /**
     * Updates the cache with given settings or fill it first.
     * @param data PrivacySettings you want to store in cache
     */
    public void updateOrSaveSettings(PrivacySettings data) {
        if(data == null) {
            PrivacyDebugger.e(TAG,"passed NULL as parameter to updateOrSaveSettings(), return");
            return;
        }
        synchronized(mCache) {
            mCache.put(data.getPackageName(), data);
            PrivacyDebugger.i(TAG, "put package: " + data.getPackageName() + " to cache");
        }
    }

    /**
     * deletes the given entry from cache
     * @param packageName packagename of application 
     */
    public void deleteSettings(String packageName) {
        if(packageName == null) {
            PrivacyDebugger.e(TAG,"passed NULL as parameter to deleteSettings(), return");
            return;
        }
        synchronized(mCache) {
            if(mCache.remove(packageName) != null)
                PrivacyDebugger.w(TAG,"removed settings for package: " + packageName + " from cache");
            else
                PrivacyDebugger.e(TAG,"got error while trying to remove settings for package: "
                        + packageName + " from cache");
        }
    }

    /**
     * 
     * @return ArrayList with all PrivacySettings which are stored in the cache
     */
    public ArrayList<PrivacySettings> getAllSetings() {
        synchronized(mCache) {
            return new ArrayList<PrivacySettings>(mCache.values());
        }
    }

    /**
     * Marks the whole settings in our cache as new entries for the database.
     * Only call this method for recovery purpose after unauthorized database access.
     */
    public void markAllAsNewEntry() {
        synchronized(mCache) {
            ArrayList<PrivacySettings> tmp = new ArrayList<PrivacySettings>(mCache.values());
            mCache.clear();
            for(PrivacySettings settings : tmp) {
                PrivacyDebugger.i(TAG,"marking settings for package: "
                        + settings.getPackageName() + " as new entry");
                mCache.put(settings.getPackageName(), PrivacySettings.markAsNewEntry(settings));
            }
        }
    }

    /**
     * Deletes the whole cache
     */
    public void removeAll() {
        synchronized(mCache) {
            mCache.clear();
            PrivacyDebugger.w(TAG,"cleared whole privacy Cache!");
        }
    }

}
