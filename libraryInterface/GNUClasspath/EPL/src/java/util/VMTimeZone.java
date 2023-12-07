/*
 *  This file is part of the Jikes RVM project (http://jikesrvm.org).
 *
 *  This file is licensed to You under the Eclipse Public License (EPL);
 *  You may not use this file except in compliance with the License. You
 *  may obtain a copy of the License at
 *
 *      http://www.opensource.org/licenses/eclipse-1.0.php
 *
 *  See the COPYRIGHT.txt file distributed with this work for information
 *  regarding copyright ownership.
 */
package java.util;

/** java.util.VMTimeZone for compatibility with GNU classpath 0.11.
 */
public class VMTimeZone {

  /**
   * This method is a no-op.<p>
   *
   * We don't need to do anything here; Jikes RVM automatically takes care
   * of this for us, since {@code bin/runrvm} always sets the
   * {@code user.timezone} property.
   *
   * @return {@code null}
   */
  static TimeZone getDefaultTimeZoneId() {
    return null;
  }

}
