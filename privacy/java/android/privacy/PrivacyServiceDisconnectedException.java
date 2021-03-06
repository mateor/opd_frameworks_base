/**
 * Copyright (C) 2012 Simeon J Morgan <smorgan@digitalfeed.net>
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

public class PrivacyServiceDisconnectedException extends PrivacyServiceException {
    private static final long serialVersionUID = 1L;
    public PrivacyServiceDisconnectedException() {}

    public PrivacyServiceDisconnectedException(String message) {
        super(message);
    }
    
    public PrivacyServiceDisconnectedException(String message, Throwable cause) {
        super(message, cause);
    }
}
