package android.privacy.utilities;

import android.content.Context;
import android.os.Binder;
import android.util.Log;
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
 * Provides Central Privacy Debugging. Use every method with ALL parameters 
 * do not pass null or something else
 * @author CollegeDev (Stefan T.)
 *
 */
public final class PrivacyDebugger {

    private static final String TAG = "PrivacyDebugger";

    private static final String TOGGLE_DEBUGGER_STATE = 
            "android.privacy.TOGGLE_DEBUGGER_STATE";

    private static final int DEBUGGER_ENABLED = 1;
    private static final int DEBUGGER_DISABLED = 2;
    private static final int DEBUGGER_UNKNOWN = -1;

    private static final String IDENTIFIER = " | PDroid2.0_debug";

    private static int DEBUGGER_STATE = DEBUGGER_UNKNOWN;

    private static boolean enabled = true;

    /**
     * used for method overloading. Quick and dirty
     * TODO: better way if there is more spare time!
     */
    private final static NoException helpParam = new NoException();

    public PrivacyDebugger () {
        Log.i(TAG,"log enabled - constructor");
        new Thread(new Runnable() {
            public void run() {
                try {
                    Thread.sleep(10000);
                } catch (InterruptedException e) {
                    //nothing here
                } finally {
                    if(DEBUGGER_STATE == DEBUGGER_UNKNOWN) {
                            enabled = false;
                            Log.i(TAG,"disabled log, because nothing changed");
                    } else {
                        Log.w(TAG,"let log enabled, because user wants it?");
                    }
                }
            }
        }).start();
    }

    /**
     * Used to enabled, disable the debugger. Requires permission
     * android.privacy.TOGGLE_DEBUGGER_STATE
     * @param state true - enabled , false - disabled
     * @param context
     */
    public static void setDebuggerState(boolean state, Context context) { 
            context.enforceCallingPermission(TOGGLE_DEBUGGER_STATE, "Requires 
            TOGGLE_DEBUGGER_STATE");
        if(state)
            DEBUGGER_STATE = DEBUGGER_ENABLED;
        else
            DEBUGGER_STATE = DEBUGGER_DISABLED;
        enabled = state;
    }

    /**
     * Tries to get last calling packageName
     * @return packageName or null
     */
    private static String getCallingPackage() {
        String[] tmp = ResolveHelper.getCallingPackageName(Binder.getCallingUid());
        if(tmp != null && tmp.length > 0)
            return tmp[0];
        else
            return null;
    }

    public static void i(String TAG, String msg) {
        i(TAG, msg, helpParam);
    }

    public static void w(String TAG, String msg) {
        w(TAG, msg, helpParam);
    }

    public static void e(String TAG, String msg) {
            e(TAG, msg, helpParam);
    }

    public static void d(String TAG, String msg) {
            d(TAG, msg, helpParam);
    }

    public static void i(String TAG, String msg, Throwable exception) {
            if (enabled && TAG != null && msg != null && exception != null) {
                String tmpPackage = getCallingPackage();
            if(tmpPackage != null) {
                    if(!exception.equals(helpParam))
                Log.i(TAG,msg + " - called from package: " + tmpPackage + ". Exception: " 
                        + Log.getStackTraceString(exception) + IDENTIFIER);
                else
                    Log.i(TAG,msg + " - called from package: " + tmpPackage + IDENTIFIER);
            } else {
                if(!exception.equals(helpParam))
                    Log.i(TAG,msg + " - called from package: UNKNOWN" + ". Exception: "
                            + Log.getStackTraceString(exception) + IDENTIFIER);
                else
                    Log.i(TAG,msg + " - called from package: UNKNOWN" + IDENTIFIER);
            }
        }
    }

    public static void w(String TAG, String msg, Throwable exception) {
        if (enabled && TAG != null && msg != null && exception != null) {
            String tmpPackage = getCallingPackage();
            if(tmpPackage != null) {
                if(!exception.equals(helpParam))
                    Log.w(TAG,msg + " - called from package: " + tmpPackage + ". Exception: " 
                    + Log.getStackTraceString(exception) + IDENTIFIER);
                else
                    Log.w(TAG,msg + " - called from package: " + tmpPackage + IDENTIFIER);
            } else {
                if(!exception.equals(helpParam))
                    Log.w(TAG,msg + " - called from package: UNKNOWN" + ". Exception: " 
                            + Log.getStackTraceString(exception) + IDENTIFIER);
                else
                    Log.w(TAG,msg + " - called from package: UNKNOWN" + IDENTIFIER);
            }
        }
    }

    public static void e(String TAG, String msg, Throwable exception) {
        if (enabled && TAG != null && msg != null && exception != null) {
            String tmpPackage = getCallingPackage();
            if(tmpPackage != null) {
                if(!exception.equals(helpParam))
                    Log.e(TAG,msg + " - called from package: " + tmpPackage + ". Exception: " 
                            + Log.getStackTraceString(exception) + IDENTIFIER);
                else
                    Log.e(TAG,msg + " - called from package: " + tmpPackage + IDENTIFIER);
            } else {
                if(!exception.equals(helpParam))
                    Log.e(TAG,msg + " - called from package: UNKNOWN" + ". Exception: " 
                            + Log.getStackTraceString(exception) + IDENTIFIER);
                else
                    Log.e(TAG,msg + " - called from package: UNKNOWN" + IDENTIFIER);
            }
        }
    }

    public static void d(String TAG, String msg, Throwable exception) {
        if (enabled && TAG != null && msg != null && exception != null) {
            String tmpPackage = getCallingPackage();
            if(tmpPackage != null) {
                if(!exception.equals(helpParam))
                    Log.d(TAG,msg + " - called from package: " + tmpPackage + ". Exception: " 
                            + Log.getStackTraceString(exception) + IDENTIFIER);
                else
                    Log.d(TAG,msg + " - called from package: " + tmpPackage + IDENTIFIER);
            } else {
                if(!exception.equals(helpParam))
                    Log.d(TAG,msg + " - called from package: UNKNOWN" + ". Exception: " 
                            + Log.getStackTraceString(exception) + IDENTIFIER);
                else
                    Log.d(TAG,msg + " - called from package: UNKNOWN" + IDENTIFIER);
            }
        }
    }

    public static void i(String TAG, String msg, String packageName) {
        i(TAG, msg, packageName, helpParam);
    }

    public static void w(String TAG, String msg, String packageName) {
        w(TAG, msg, packageName, helpParam);
    }

    public static void e(String TAG, String msg, String packageName) {
        e(TAG, msg, packageName, helpParam);
    }

    public static void d(String TAG, String msg, String packageName) {
        d(TAG, msg, packageName, helpParam);
    }

    public static void i(String TAG, String msg, String packageName, Throwable exception) {
        if(enabled && TAG != null && msg != null && packageName 
                != null && !exception.equals(helpParam)) 
            Log.i(TAG,msg + " - from package: " + packageName + ". Exception: " 
                    + Log.getStackTraceString(exception) + IDENTIFIER);	
        else if(enabled && TAG != null && msg != null && packageName != null 
                && exception.equals(helpParam))
            Log.i(TAG,msg + " - from package: " + packageName + IDENTIFIER);
        else if(enabled && TAG != null && msg != null) {
            //try to get calling package
            i(TAG,msg);
        }
    }

    public static void w(String TAG, String msg, String packageName, Throwable exception) {
        if(enabled && TAG != null && msg != null && packageName != null 
                && !exception.equals(helpParam)) 
            Log.w(TAG,msg + " - from package: " + packageName + ". Exception: " 
                    + Log.getStackTraceString(exception) + IDENTIFIER);
        else if(enabled && TAG != null && msg != null && packageName != null 
                && exception.equals(helpParam))
            Log.w(TAG,msg + " - from package: " + packageName + IDENTIFIER);
        else if(enabled && TAG != null && msg != null) {
            //try to get calling package
            w(TAG,msg);
        }
    }

    public static void e(String TAG, String msg, String packageName, Throwable exception) {
        if(enabled && TAG != null && msg != null && packageName != null 
                && !exception.equals(helpParam)) 
            Log.e(TAG,msg + " - from package: " + packageName + ". Exception: " 
                    + Log.getStackTraceString(exception) + IDENTIFIER);
        else if(enabled && TAG != null && msg != null && packageName != null 
                && exception.equals(helpParam))
            Log.e(TAG,msg + " - from package: " + packageName + IDENTIFIER);
        else if(enabled && TAG != null && msg != null) {
            //try to get calling package
            e(TAG,msg);
        }
    }

    public static void d(String TAG, String msg, String packageName, Throwable exception) {
        if(enabled && TAG != null && msg != null && packageName != null 
                && !exception.equals(helpParam)) 
            Log.d(TAG,msg + " - from package: " + packageName + ". Exception: " 
                    + Log.getStackTraceString(exception) + IDENTIFIER);
        else if(enabled && TAG != null && msg != null && packageName != null 
                && exception.equals(helpParam))
            Log.d(TAG,msg + " - from package: " + packageName + IDENTIFIER);
        else if(enabled && TAG != null && msg != null) {
            //try to get calling package
            d(TAG,msg);
        }
    }

    //for method overheading purpose only
    private static final class NoException extends Throwable {

    }

}
