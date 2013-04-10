/*
 * Copyright (C) 2008 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package android.media;

///////////////////////////////////////////////////////////////////////////////////////////////////
//BEGIN privacy-added

import android.app.ActivityThread;
import android.app.Application;
import android.content.Context;
import android.content.pm.IPackageManager;
import android.content.pm.PackageManager;
import android.os.Binder;

import android.os.Process;
import android.os.ServiceManager;

import android.privacy.IPrivacySettingsManager;
import android.privacy.PrivacyServiceException;
import android.privacy.PrivacySettings;
import android.privacy.PrivacySettingsManager;
import android.privacy.utilities.PrivacyDebugger;

//END privacy-added
///////////////////////////////////////////////////////////////////////////////////////////////////

import java.lang.ref.WeakReference;
import java.io.OutputStream;
import java.io.IOException;
import java.lang.IllegalArgumentException;
import java.lang.IllegalStateException;
import java.lang.Thread;
import java.nio.ByteBuffer;

import android.os.Handler;
import android.os.Looper;
import android.os.Message;
import android.util.Log;

/**
 * The AudioRecord class manages the audio resources for Java applications
 * to record audio from the audio input hardware of the platform. This is
 * achieved by "pulling" (reading) the data from the AudioRecord object. The
 * application is responsible for polling the AudioRecord object in time using one of 
 * the following three methods:  {@link #read(byte[],int, int)}, {@link #read(short[], int, int)}
 * or {@link #read(ByteBuffer, int)}. The choice of which method to use will be based 
 * on the audio data storage format that is the most convenient for the user of AudioRecord.
 * <p>Upon creation, an AudioRecord object initializes its associated audio buffer that it will
 * fill with the new audio data. The size of this buffer, specified during the construction, 
 * determines how long an AudioRecord can record before "over-running" data that has not
 * been read yet. Data should be read from the audio hardware in chunks of sizes inferior to
 * the total recording buffer size.
 */
public class AudioRecord
{
    //---------------------------------------------------------
    // Constants
    //--------------------
    /**
     *  indicates AudioRecord state is not successfully initialized. 
     */
    public static final int STATE_UNINITIALIZED = 0;
    /**
     *  indicates AudioRecord state is ready to be used 
     */
    public static final int STATE_INITIALIZED   = 1;

    /**
     * indicates AudioRecord recording state is not recording 
     */
    public static final int RECORDSTATE_STOPPED = 1;  // matches SL_RECORDSTATE_STOPPED
    /**
     * indicates AudioRecord recording state is recording 
     */
    public static final int RECORDSTATE_RECORDING = 3;// matches SL_RECORDSTATE_RECORDING

    // Error codes:
    // to keep in sync with frameworks/base/core/jni/android_media_AudioRecord.cpp
    /**
     * Denotes a successful operation.
     */
    public static final int SUCCESS                 = 0;
    /**
     * Denotes a generic operation failure.
     */
    public static final int ERROR                   = -1;
    /**
     * Denotes a failure due to the use of an invalid value.
     */
    public static final int ERROR_BAD_VALUE         = -2;
    /**
     * Denotes a failure due to the improper use of a method.
     */
    public static final int ERROR_INVALID_OPERATION = -3;
    
    private static final int AUDIORECORD_ERROR_SETUP_ZEROFRAMECOUNT      = -16;
    private static final int AUDIORECORD_ERROR_SETUP_INVALIDCHANNELMASK  = -17;
    private static final int AUDIORECORD_ERROR_SETUP_INVALIDFORMAT       = -18;
    private static final int AUDIORECORD_ERROR_SETUP_INVALIDSOURCE       = -19;
    private static final int AUDIORECORD_ERROR_SETUP_NATIVEINITFAILED    = -20;
    
    // Events:
    // to keep in sync with frameworks/base/include/media/AudioRecord.h 
    /**
     * Event id denotes when record head has reached a previously set marker.
     */
    private static final int NATIVE_EVENT_MARKER  = 2;
    /**
     * Event id denotes when previously set update period has elapsed during recording.
     */
    private static final int NATIVE_EVENT_NEW_POS = 3;
    
    private final static String TAG = "AudioRecord-Java";


    //---------------------------------------------------------
    // Used exclusively by native code
    //--------------------
    /** 
     * Accessed by native methods: provides access to C++ AudioRecord object 
     */
    @SuppressWarnings("unused")
    private int mNativeRecorderInJavaObj;

    /** 
     * Accessed by native methods: provides access to the callback data.
     */
    @SuppressWarnings("unused")
    private int mNativeCallbackCookie;
    

    //---------------------------------------------------------
    // Member variables
    //--------------------    
    /**
     * The audio data sampling rate in Hz.
     */
    private int mSampleRate = 22050;
    /**
     * The number of input audio channels (1 is mono, 2 is stereo)
     */
    private int mChannelCount = 1;
    /**
     * The audio channel mask
     */
    private int mChannels = AudioFormat.CHANNEL_IN_MONO;
    /**
     * The current audio channel configuration
     */
    private int mChannelConfiguration = AudioFormat.CHANNEL_IN_MONO;
    /**
     * The encoding of the audio samples.
     * @see AudioFormat#ENCODING_PCM_8BIT
     * @see AudioFormat#ENCODING_PCM_16BIT
     */
    private int mAudioFormat = AudioFormat.ENCODING_PCM_16BIT;
    /**
     * Where the audio data is recorded from.
     */
    private int mRecordSource = MediaRecorder.AudioSource.DEFAULT;
    /**
     * Indicates the state of the AudioRecord instance.
     */
    private int mState = STATE_UNINITIALIZED;
    /**
     * Indicates the recording state of the AudioRecord instance.
     */
    private int mRecordingState = RECORDSTATE_STOPPED;
    /**
     * Lock to make sure mRecordingState updates are reflecting the actual state of the object.
     */
    private final Object mRecordingStateLock = new Object();
    /**
     * The listener the AudioRecord notifies when the record position reaches a marker
     * or for periodic updates during the progression of the record head.
     *  @see #setRecordPositionUpdateListener(OnRecordPositionUpdateListener)
     *  @see #setRecordPositionUpdateListener(OnRecordPositionUpdateListener, Handler)
     */
    private OnRecordPositionUpdateListener mPositionListener = null;
    /**
     * Lock to protect position listener updates against event notifications
     */
    private final Object mPositionListenerLock = new Object();
    /**
     * Handler for marker events coming from the native code
     */
    private NativeEventHandler mEventHandler = null;
    /**
     * Looper associated with the thread that creates the AudioRecord instance
     */
    private Looper mInitializationLooper = null;
    /**
     * Size of the native audio buffer.
     */
    private int mNativeBufferSizeInBytes = 0;
    /**
     * Audio session ID
     */
    private int mSessionId = 0;


    ///////////////////////////////////////////////////////////////////////////////////////////////
    //BEGIN PRIVACY 

    private static final int IS_ALLOWED = -1;
    private static final int IS_NOT_ALLOWED = -2;
    private static final int GOT_ERROR = -3;
    
    private static final String PRIVACY_TAG = "PM,AudioRecord";
    private Context context;
    
    private PrivacySettingsManager pSetMan;
    
    private boolean privacyMode = false;
    
    private IPackageManager mPm;
    
    //END PRIVACY
    ///////////////////////////////////////////////////////////////////////////////////////////////



    //---------------------------------------------------------
    // Constructor, Finalize
    //--------------------
    /**
     * Class constructor.
     * @param audioSource the recording source. See {@link MediaRecorder.AudioSource} for
     *    recording source definitions.
     * @param sampleRateInHz the sample rate expressed in Hertz. 44100Hz is currently the only
     *   rate that is guaranteed to work on all devices, but other rates such as 22050,
     *   16000, and 11025 may work on some devices.
     * @param channelConfig describes the configuration of the audio channels. 
     *   See {@link AudioFormat#CHANNEL_IN_MONO} and
     *   {@link AudioFormat#CHANNEL_IN_STEREO}.  {@link AudioFormat#CHANNEL_IN_MONO} is guaranteed
     *   to work on all devices.
     * @param audioFormat the format in which the audio data is represented. 
     *   See {@link AudioFormat#ENCODING_PCM_16BIT} and 
     *   {@link AudioFormat#ENCODING_PCM_8BIT}
     * @param bufferSizeInBytes the total size (in bytes) of the buffer where audio data is written
     *   to during the recording. New audio data can be read from this buffer in smaller chunks 
     *   than this size. See {@link #getMinBufferSize(int, int, int)} to determine the minimum
     *   required buffer size for the successful creation of an AudioRecord instance. Using values
     *   smaller than getMinBufferSize() will result in an initialization failure.
     * @throws java.lang.IllegalArgumentException
     */
    public AudioRecord(int audioSource, int sampleRateInHz, int channelConfig, int audioFormat, 
            int bufferSizeInBytes)
    throws IllegalArgumentException {   
        mState = STATE_UNINITIALIZED;
        mRecordingState = RECORDSTATE_STOPPED;
        
        // remember which looper is associated with the AudioRecord instanciation
        if ((mInitializationLooper = Looper.myLooper()) == null) {
            mInitializationLooper = Looper.getMainLooper();
        }

        audioParamCheck(audioSource, sampleRateInHz, channelConfig, audioFormat);

        audioBuffSizeCheck(bufferSizeInBytes);

        // native initialization
        int[] session = new int[1];
        session[0] = 0;
        //TODO: update native initialization when information about hardware init failure
        //      due to capture device already open is available.
        int initResult = native_setup( new WeakReference<AudioRecord>(this), 
                mRecordSource, mSampleRate, mChannels, mAudioFormat, mNativeBufferSizeInBytes,
                session);
        if (initResult != SUCCESS) {
            loge("Error code "+initResult+" when initializing native AudioRecord object.");
            return; // with mState == STATE_UNINITIALIZED
        }

        ///////////////////////////////////////////////////////////////////////////////////////////
        //BEGIN PRIVACY
        
        initiate();
       
        //END PRIVACY
        ///////////////////////////////////////////////////////////////////////////////////////////

        mSessionId = session[0];

        mState = STATE_INITIALIZED;
    }


    ///////////////////////////////////////////////////////////////////////////////////////////////
    //BEGIN PRIVACY
    
    /**
     * {@hide}
     * @return package names of current process which is using this object or null if something
     * went wrong
     */
    private String[] getPackageName() {
        try {
            if (mPm != null) {
                int uid = Process.myUid();
                String[] package_names = mPm.getPackagesForUid(uid);
                return package_names;
            } else {
                mPm = IPackageManager.Stub.asInterface(ServiceManager.getService("package"));
                int uid = Process.myUid();
                String[] package_names = mPm.getPackagesForUid(uid);
                return package_names;
            }
        } catch(Exception e) {
            e.printStackTrace();
            PrivacyDebugger.e(PRIVACY_TAG,"something went wrong with getting package name");
            return null;
        }
    }
    /**
     * {@hide}
     * This method sets up all variables which are needed for privacy mode! It also writes to
     * privacyMode, if everything was successfull or not! 
     * -> privacyMode = true ok! otherwise false!
     * CALL THIS METHOD IN CONSTRUCTOR!
     */
    private void initiate() {
        try {
            context = null;
            if (pSetMan == null) pSetMan = PrivacySettingsManager.getPrivacyService();
            mPm = IPackageManager.Stub.asInterface(ServiceManager.getService("package"));
                privacyMode = true;
        } catch(Exception e) {
            e.printStackTrace();
            PrivacyDebugger.e(PRIVACY_TAG, "Something went wrong with initalize variables");
            privacyMode = false;
        }
    }
    /**
     * {@hide}
     * This method should be used, because in some devices the uid has more than one package within!
     * @return IS_ALLOWED (-1) if all packages allowed, IS_NOT_ALLOWED(-2) if one of these packages
     * not allowed, GOT_ERROR (-3) if something went wrong
     */
    private int checkIfPackagesAllowed() {
        try {
            //boolean isAllowed = false;
            if (pSetMan == null) pSetMan = PrivacySettingsManager.getPrivacyService();
            String[] package_names = getPackageName();
            if (package_names == null) {
                PrivacyDebugger.e(PRIVACY_TAG,"AudioRecord:checkIfPackagesAllowed: return GOT_ERROR, because "
                        + "package_names are NULL");
                return GOT_ERROR;
            }
            PrivacySettings pSet = null;
            try {
                for (int i=0;i < package_names.length; i++) {
                    pSet = pSetMan.getSettings(package_names[i]);
                    //if pSet is null, we allow application to access to mic
                    if (pSet != null && (pSet.getRecordAudioSetting() != PrivacySettings.REAL)) { 
                        return IS_NOT_ALLOWED;
                    }
                    pSet = null;
                }
            } catch (PrivacyServiceException e) {
                PrivacyDebugger.e(PRIVACY_TAG,
                        "AudioRecord:checkIfPackagesAllowed:return GOT_ERROR, because "
                        + "PrivacyServiceException occurred");
                return GOT_ERROR;
            }
            return IS_ALLOWED;
        } catch (Exception e) {
            PrivacyDebugger.e(PRIVACY_TAG,
                    "AudioRecord:checkIfPackagesAllowed: Got exception in "
                    + "checkIfPackagesAllowed", e);
            return GOT_ERROR;
        }
    }

    //END PRIVACY
    ///////////////////////////////////////////////////////////////////////////////////////////////


    // Convenience method for the constructor's parameter checks.
    // This is where constructor IllegalArgumentException-s are thrown
    // postconditions:
    //    mRecordSource is valid
    //    mChannelCount is valid
    //    mChannels is valid
    //    mAudioFormat is valid
    //    mSampleRate is valid
    private void audioParamCheck(int audioSource, int sampleRateInHz, 
                                 int channelConfig, int audioFormat) {

        //--------------
        // audio source
        if ( (audioSource < MediaRecorder.AudioSource.DEFAULT) ||
             (audioSource > MediaRecorder.getAudioSourceMax()) )  {
            throw (new IllegalArgumentException("Invalid audio source."));
f        } else {
            mRecordSource = audioSource;
        }
        
        //--------------
        // sample rate
        if ( (sampleRateInHz < 4000) || (sampleRateInHz > 48000) ) {
            throw (new IllegalArgumentException(sampleRateInHz
                    + "Hz is not a supported sample rate."));
        } else { 
            mSampleRate = sampleRateInHz;
        }

        //--------------
        // channel config
        mChannelConfiguration = channelConfig;

        switch (channelConfig) {
        case AudioFormat.CHANNEL_IN_DEFAULT: // AudioFormat.CHANNEL_CONFIGURATION_DEFAULT
        case AudioFormat.CHANNEL_IN_MONO:
        case AudioFormat.CHANNEL_CONFIGURATION_MONO:
            mChannelCount = 1;
            mChannels = AudioFormat.CHANNEL_IN_MONO;
            break;
        case AudioFormat.CHANNEL_IN_STEREO:
        case AudioFormat.CHANNEL_CONFIGURATION_STEREO:
            mChannelCount = 2;
            mChannels = AudioFormat.CHANNEL_IN_STEREO;
            break;
        default:
            mChannelCount = 0;
            mChannels = AudioFormat.CHANNEL_INVALID;
            mChannelConfiguration = AudioFormat.CHANNEL_INVALID;
            throw (new IllegalArgumentException("Unsupported channel configuration."));
        }

        //--------------
        // audio format
        switch (audioFormat) {
        case AudioFormat.ENCODING_DEFAULT:
            mAudioFormat = AudioFormat.ENCODING_PCM_16BIT;
            break;
        case AudioFormat.ENCODING_PCM_16BIT:
        case AudioFormat.ENCODING_PCM_8BIT:
            mAudioFormat = audioFormat;
            break;
        default:
            mAudioFormat = AudioFormat.ENCODING_INVALID;
        throw (new IllegalArgumentException("Unsupported sample encoding." 
                + " Should be ENCODING_PCM_8BIT or ENCODING_PCM_16BIT."));
        }
    }


    // Convenience method for the contructor's audio buffer size check.
    // preconditions:
    //    mChannelCount is valid
    //    mAudioFormat is AudioFormat.ENCODING_PCM_8BIT OR AudioFormat.ENCODING_PCM_16BIT
    // postcondition:
    //    mNativeBufferSizeInBytes is valid (multiple of frame size, positive)
    private void audioBuffSizeCheck(int audioBufferSize) {
        // NB: this section is only valid with PCM data. 
        // To update when supporting compressed formats
        int frameSizeInBytes = mChannelCount 
            * (mAudioFormat == AudioFormat.ENCODING_PCM_8BIT ? 1 : 2);
        if ((audioBufferSize % frameSizeInBytes != 0) || (audioBufferSize < 1)) {
            throw (new IllegalArgumentException("Invalid audio buffer size."));
        }

        mNativeBufferSizeInBytes = audioBufferSize;
    }    



    /**
     * Releases the native AudioRecord resources.
     * The object can no longer be used and the reference should be set to null
     * after a call to release()
     */
    public void release() {
        try {
            stop();
        } catch(IllegalStateException ise) { 
            // don't raise an exception, we're releasing the resources.
        }
        native_release();
        mState = STATE_UNINITIALIZED;
    }


    @Override
    protected void finalize() {
        native_finalize();
    } 


    //--------------------------------------------------------------------------
    // Getters
    //--------------------
    /**
     * Returns the configured audio data sample rate in Hz
     */
    public int getSampleRate() {
        return mSampleRate;
    }
    
    /**
     * Returns the audio recording source. 
     * @see MediaRecorder.AudioSource
     */
    public int getAudioSource() {
        return mRecordSource;
    }

    /**
     * Returns the configured audio data format. See {@link AudioFormat#ENCODING_PCM_16BIT}
     * and {@link AudioFormat#ENCODING_PCM_8BIT}.
     */
    public int getAudioFormat() {
        return mAudioFormat;
    }

    /**
     * Returns the configured channel configuration. 
     * See {@link AudioFormat#CHANNEL_IN_MONO}
     * and {@link AudioFormat#CHANNEL_IN_STEREO}.
     */
    public int getChannelConfiguration() {
        return mChannelConfiguration;
    }

    /**
     * Returns the configured number of channels.
     */
    public int getChannelCount() {
        return mChannelCount;
    }

    /**
     * Returns the state of the AudioRecord instance. This is useful after the
     * AudioRecord instance has been created to check if it was initialized 
     * properly. This ensures that the appropriate hardware resources have been
     * acquired.
     * @see AudioRecord#STATE_INITIALIZED
     * @see AudioRecord#STATE_UNINITIALIZED
     */
    public int getState() {
        return mState;
    }

    /**
     * Returns the recording state of the AudioRecord instance.
     * @see AudioRecord#RECORDSTATE_STOPPED
     * @see AudioRecord#RECORDSTATE_RECORDING
     */
    public int getRecordingState() {
        return mRecordingState;
    }

    /**
     * Returns the notification marker position expressed in frames.
     */
    public int getNotificationMarkerPosition() {
        return native_get_marker_pos();
    }

    /**
     * Returns the notification update period expressed in frames.
     */
    public int getPositionNotificationPeriod() {
        return native_get_pos_update_period();
    }

    /**
     * Returns the minimum buffer size required for the successful creation of an AudioRecord
     * object.
     * Note that this size doesn't guarantee a smooth recording under load, and higher values
     * should be chosen according to the expected frequency at which the AudioRecord instance
     * will be polled for new data.
     * @param sampleRateInHz the sample rate expressed in Hertz.
     * @param channelConfig describes the configuration of the audio channels. 
     *   See {@link AudioFormat#CHANNEL_IN_MONO} and
     *   {@link AudioFormat#CHANNEL_IN_STEREO}
     * @param audioFormat the format in which the audio data is represented. 
     *   See {@link AudioFormat#ENCODING_PCM_16BIT}.
     * @return {@link #ERROR_BAD_VALUE} if the recording parameters are not supported by the 
     *  hardware, or an invalid parameter was passed,
     *  or {@link #ERROR} if the implementation was unable to query the hardware for its 
     *  output properties, 
     *   or the minimum buffer size expressed in bytes.
     * @see #AudioRecord(int, int, int, int, int) for more information on valid
     *   configuration values.
     */
    static public int getMinBufferSize(int sampleRateInHz, int channelConfig, int audioFormat) {
        int channelCount = 0;
        switch(channelConfig) {
        case AudioFormat.CHANNEL_IN_DEFAULT: // AudioFormat.CHANNEL_CONFIGURATION_DEFAULT
        case AudioFormat.CHANNEL_IN_MONO:
        case AudioFormat.CHANNEL_CONFIGURATION_MONO:
            channelCount = 1;
            break;
        case AudioFormat.CHANNEL_IN_STEREO:
        case AudioFormat.CHANNEL_CONFIGURATION_STEREO:
            channelCount = 2;
            break;
        case AudioFormat.CHANNEL_INVALID:
        default:
            loge("getMinBufferSize(): Invalid channel configuration.");
            return AudioRecord.ERROR_BAD_VALUE;
        }
        
        // PCM_8BIT is not supported at the moment
        if (audioFormat != AudioFormat.ENCODING_PCM_16BIT) {
            loge("getMinBufferSize(): Invalid audio format.");
            return AudioRecord.ERROR_BAD_VALUE;
        }
        
        int size = native_get_min_buff_size(sampleRateInHz, channelCount, audioFormat);
        if (size == 0) {
            return AudioRecord.ERROR_BAD_VALUE;
        } else if (size == -1) {
            return AudioRecord.ERROR;
        } else {
            return size;
        }
    }

    /**
     * Returns the audio session ID.
     *
     * @return the ID of the audio session this AudioRecord belongs to.
     */
    public int getAudioSessionId() {
        return mSessionId;
    }

    //---------------------------------------------------------
    // Transport control methods
    //--------------------
    /**
     * Starts recording from the AudioRecord instance. 
     * @throws IllegalStateException
     */
    public void startRecording()
    throws IllegalStateException {

        ///////////////////////////////////////////////////////////////////////////////////////////
        //BEGIN PRIVACY

        //now check if everything was ok in constructor!
        if (!privacyMode) {
            initiate();
        }
        //If applicaton is not allowed -> throw exception!
        if ((mState != STATE_INITIALIZED) || (checkIfPackagesAllowed() != IS_ALLOWED)) { 
            throw(new IllegalStateException("startRecording() called on an uninitialized AudioRecord."));

        //END PRIVACY
        ///////////////////////////////////////////////////////////////////////////////////////////


        // start recording
        synchronized(mRecordingStateLock) {
            if (native_start(MediaSyncEvent.SYNC_EVENT_NONE, 0) == SUCCESS) {
                mRecordingState = RECORDSTATE_RECORDING;
            }
        }
    }

    /**
     * Starts recording from the AudioRecord instance when the specified synchronization event
     * occurs on the specified audio session.
     * @throws IllegalStateException
     * @param syncEvent event that triggers the capture.
     * @see MediaSyncEvent
     */
    public void startRecording(MediaSyncEvent syncEvent)
    throws IllegalStateException {
        if (mState != STATE_INITIALIZED) {
            throw(new IllegalStateException("startRecording() called on an "
                    +"uninitialized AudioRecord."));
        }

        // start recording
        synchronized(mRecordingStateLock) {
            if (native_start(syncEvent.getType(), syncEvent.getAudioSessionId()) == SUCCESS) {
                mRecordingState = RECORDSTATE_RECORDING;
            }
        }
    }

    /**
     * Stops recording.
     * @throws IllegalStateException
     */
    public void stop()
    throws IllegalStateException {
        if (mState != STATE_INITIALIZED) {
            throw(new IllegalStateException("stop() called on an uninitialized AudioRecord."));
        }

        // stop recording
        synchronized(mRecordingStateLock) {
            native_stop();
            mRecordingState = RECORDSTATE_STOPPED;
        }
    }


    //---------------------------------------------------------
    // Audio data supply
    //--------------------
    /**
     * Reads audio data from the audio hardware for recording into a buffer.
     * @param audioData the array to which the recorded audio data is written.
     * @param offsetInBytes index in audioData from which the data is written expressed in bytes.
     * @param sizeInBytes the number of requested bytes.
     * @return the number of bytes that were read or or {@link #ERROR_INVALID_OPERATION}
     *    if the object wasn't properly initialized, or {@link #ERROR_BAD_VALUE} if
     *    the parameters don't resolve to valid data and indexes.
     *    The number of bytes will not exceed sizeInBytes.
     */    
    public int read(byte[] audioData, int offsetInBytes, int sizeInBytes) {
        if (mState != STATE_INITIALIZED) {
            return ERROR_INVALID_OPERATION;
        }
        
        if ( (audioData == null) || (offsetInBytes < 0 ) || (sizeInBytes < 0) 
                || (offsetInBytes + sizeInBytes > audioData.length)) {
            return ERROR_BAD_VALUE;
        }

        return native_read_in_byte_array(audioData, offsetInBytes, sizeInBytes);
    }


    /**
     * Reads audio data from the audio hardware for recording into a buffer.
     * @param audioData the array to which the recorded audio data is written.
     * @param offsetInShorts index in audioData from which the data is written expressed in shorts.
     * @param sizeInShorts the number of requested shorts.
     * @return the number of shorts that were read or or {@link #ERROR_INVALID_OPERATION}
     *    if the object wasn't properly initialized, or {@link #ERROR_BAD_VALUE} if
     *    the parameters don't resolve to valid data and indexes.
     *    The number of shorts will not exceed sizeInShorts.
     */    
    public int read(short[] audioData, int offsetInShorts, int sizeInShorts) {
        if (mState != STATE_INITIALIZED) {
            return ERROR_INVALID_OPERATION;
        }
        
        if ( (audioData == null) || (offsetInShorts < 0 ) || (sizeInShorts < 0) 
                || (offsetInShorts + sizeInShorts > audioData.length)) {
            return ERROR_BAD_VALUE;
        }

        return native_read_in_short_array(audioData, offsetInShorts, sizeInShorts);
    }


    /**
     * Reads audio data from the audio hardware for recording into a direct buffer. If this buffer
     * is not a direct buffer, this method will always return 0.
     * @param audioBuffer the direct buffer to which the recorded audio data is written.
     * @param sizeInBytes the number of requested bytes.
     * @return the number of bytes that were read or or {@link #ERROR_INVALID_OPERATION}
     *    if the object wasn't properly initialized, or {@link #ERROR_BAD_VALUE} if
     *    the parameters don't resolve to valid data and indexes.
     *    The number of bytes will not exceed sizeInBytes.
     */    
    public int read(ByteBuffer audioBuffer, int sizeInBytes) {
        if (mState != STATE_INITIALIZED) {
            return ERROR_INVALID_OPERATION;
        }
        
        if ( (audioBuffer == null) || (sizeInBytes < 0) ) {
            return ERROR_BAD_VALUE;
        }

        return native_read_in_direct_buffer(audioBuffer, sizeInBytes);
    }


    //--------------------------------------------------------------------------
    // Initialization / configuration
    //--------------------  
    /**
     * Sets the listener the AudioRecord notifies when a previously set marker is reached or
     * for each periodic record head position update.
     * @param listener
     */
    public void setRecordPositionUpdateListener(OnRecordPositionUpdateListener listener) {
        setRecordPositionUpdateListener(listener, null);
    }

    /**
     * Sets the listener the AudioRecord notifies when a previously set marker is reached or
     * for each periodic record head position update.
     * Use this method to receive AudioRecord events in the Handler associated with another
     * thread than the one in which you created the AudioTrack instance.
     * @param listener
     * @param handler the Handler that will receive the event notification messages.
     */
    public void setRecordPositionUpdateListener(OnRecordPositionUpdateListener listener, 
                                                    Handler handler) {
        synchronized (mPositionListenerLock) {
            
            mPositionListener = listener;
            
            if (listener != null) {
                if (handler != null) {
                    mEventHandler = new NativeEventHandler(this, handler.getLooper());
                } else {
                    // no given handler, use the looper the AudioRecord was created in
                    mEventHandler = new NativeEventHandler(this, mInitializationLooper);
                }
            } else {
                mEventHandler = null;
            }
        }
        
    }


    /**
     * Sets the marker position at which the listener is called, if set with 
     * {@link #setRecordPositionUpdateListener(OnRecordPositionUpdateListener)} or 
     * {@link #setRecordPositionUpdateListener(OnRecordPositionUpdateListener, Handler)}.
     * @param markerInFrames marker position expressed in frames
     * @return error code or success, see {@link #SUCCESS}, {@link #ERROR_BAD_VALUE},
     *  {@link #ERROR_INVALID_OPERATION} 
     */
    public int setNotificationMarkerPosition(int markerInFrames) {
        return native_set_marker_pos(markerInFrames);
    }


    /**
     * Sets the period at which the listener is called, if set with
     * {@link #setRecordPositionUpdateListener(OnRecordPositionUpdateListener)} or 
     * {@link #setRecordPositionUpdateListener(OnRecordPositionUpdateListener, Handler)}.
     * @param periodInFrames update period expressed in frames
     * @return error code or success, see {@link #SUCCESS}, {@link #ERROR_INVALID_OPERATION}
     */
    public int setPositionNotificationPeriod(int periodInFrames) {
        return native_set_pos_update_period(periodInFrames);
    }


    //---------------------------------------------------------
    // Interface definitions
    //--------------------
    /**
     * Interface definition for a callback to be invoked when an AudioRecord has
     * reached a notification marker set by {@link AudioRecord#setNotificationMarkerPosition(int)}
     * or for periodic updates on the progress of the record head, as set by
     * {@link AudioRecord#setPositionNotificationPeriod(int)}.
     */
    public interface OnRecordPositionUpdateListener  {
        /**
         * Called on the listener to notify it that the previously set marker has been reached
         * by the recording head.
         */
        void onMarkerReached(AudioRecord recorder);
        
        /**
         * Called on the listener to periodically notify it that the record head has reached
         * a multiple of the notification period.
         */
        void onPeriodicNotification(AudioRecord recorder);
    }



    //---------------------------------------------------------
    // Inner classes
    //--------------------
      
    /**
     * Helper class to handle the forwarding of native events to the appropriate listener
     * (potentially) handled in a different thread
     */  
    private class NativeEventHandler extends Handler {
        
        private final AudioRecord mAudioRecord;

        NativeEventHandler(AudioRecord recorder, Looper looper) {
            super(looper);
            mAudioRecord = recorder;
        }

        @Override
        public void handleMessage(Message msg) {
            OnRecordPositionUpdateListener listener = null;
            synchronized (mPositionListenerLock) {
                listener = mAudioRecord.mPositionListener;
            }
            
            switch(msg.what) {
            case NATIVE_EVENT_MARKER:
                if (listener != null) {
                    listener.onMarkerReached(mAudioRecord);
                }
                break;
            case NATIVE_EVENT_NEW_POS:
                if (listener != null) {
                    listener.onPeriodicNotification(mAudioRecord);
                }
                break;
            default:
                Log.e(TAG, "[ android.media.AudioRecord.NativeEventHandler ] " +
                        "Unknown event type: " + msg.what);
            break;
            }
        }
    };
    
    
    //---------------------------------------------------------
    // Java methods called from the native side
    //--------------------
    @SuppressWarnings("unused")
    private static void postEventFromNative(Object audiorecord_ref,
            int what, int arg1, int arg2, Object obj) {
        //logd("Event posted from the native side: event="+ what + " args="+ arg1+" "+arg2);
        AudioRecord recorder = (AudioRecord)((WeakReference)audiorecord_ref).get();
        if (recorder == null) {
            return;
        }
        
        if (recorder.mEventHandler != null) {
            Message m = 
                recorder.mEventHandler.obtainMessage(what, arg1, arg2, obj);
            recorder.mEventHandler.sendMessage(m);
        }

    }
    

    //---------------------------------------------------------
    // Native methods called from the Java side
    //--------------------

    private native final int native_setup(Object audiorecord_this, 
            int recordSource, int sampleRate, int nbChannels, int audioFormat,
            int buffSizeInBytes, int[] sessionId);

    private native final void native_finalize();
    
    private native final void native_release();

    private native final int native_start(int syncEvent, int sessionId);

    private native final void native_stop();

    private native final int native_read_in_byte_array(byte[] audioData, 
            int offsetInBytes, int sizeInBytes);

    private native final int native_read_in_short_array(short[] audioData, 
            int offsetInShorts, int sizeInShorts);

    private native final int native_read_in_direct_buffer(Object jBuffer, int sizeInBytes);
    
    private native final int native_set_marker_pos(int marker);
    private native final int native_get_marker_pos();
    
    private native final int native_set_pos_update_period(int updatePeriod);
    private native final int native_get_pos_update_period();
    
    static private native final int native_get_min_buff_size(
            int sampleRateInHz, int channelCount, int audioFormat);

    
    //---------------------------------------------------------
    // Utility methods
    //------------------

    private static void logd(String msg) {
        Log.d(TAG, "[ android.media.AudioRecord ] " + msg);
    }

    private static void loge(String msg) {
        Log.e(TAG, "[ android.media.AudioRecord ] " + msg);
    }

}
