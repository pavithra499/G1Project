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
package org.mmtk.utility.options;

public class G1GCLiveThresholdPercent extends org.vmutil.options.FloatOption {
  /**
   * Create the option.
   */
  public G1GCLiveThresholdPercent() {
    super(Options.set, "G1 GC Live Threshold Percent",
          "Sets the occupancy threshold for an region to be included in a G1 garbage collection cycle. The default occupancy is 65 percent.",
          65f);
  }

  /**
   * Ensure the value is valid.
   */
  @Override
  protected void validate() {
    failIf((this.value < 0 || this.value > 100.0), "Ratio must be a float between 0 and 100");
  }
}
