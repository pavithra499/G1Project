package org.jikesrvm.runtime;

import javax.annotation.Generated;

@org.vmmagic.pragma.Uninterruptible
@Generated(
value = "org.jikesrvm.tools.annotation_processing.SysCallProcessor",
comments = "Auto-generated from org.jikesrvm.runtime.SysCall")
public final class SysCallImpl extends org.jikesrvm.runtime.SysCall {

  @java.lang.Override
  public void sysConsoleWriteChar(char v) {
    sysConsoleWriteChar(BootRecord.the_boot_record.sysConsoleWriteCharIP, v);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysConsoleWriteChar(org.vmmagic.unboxed.Address nativeIP, char v);

  @java.lang.Override
  public void sysConsoleWriteInteger(int value, int hexToo) {
    sysConsoleWriteInteger(BootRecord.the_boot_record.sysConsoleWriteIntegerIP, value, hexToo);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysConsoleWriteInteger(org.vmmagic.unboxed.Address nativeIP, int value, int hexToo);

  @java.lang.Override
  public void sysConsoleWriteLong(long value, int hexToo) {
    sysConsoleWriteLong(BootRecord.the_boot_record.sysConsoleWriteLongIP, value, hexToo);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysConsoleWriteLong(org.vmmagic.unboxed.Address nativeIP, long value, int hexToo);

  @java.lang.Override
  public void sysConsoleWriteDouble(double value, int postDecimalDigits) {
    sysConsoleWriteDouble(BootRecord.the_boot_record.sysConsoleWriteDoubleIP, value, postDecimalDigits);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysConsoleWriteDouble(org.vmmagic.unboxed.Address nativeIP, double value, int postDecimalDigits);

  @java.lang.Override
  public void sysConsoleFlushErrorAndTrace() {
    sysConsoleFlushErrorAndTrace(BootRecord.the_boot_record.sysConsoleFlushErrorAndTraceIP);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysConsoleFlushErrorAndTrace(org.vmmagic.unboxed.Address nativeIP);

  @java.lang.Override
  public void sysExit(int value) {
    sysExit(BootRecord.the_boot_record.sysExitIP, value);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysExit(org.vmmagic.unboxed.Address nativeIP, int value);

  @java.lang.Override
  public int sysArg(int argno, byte[] buf, int buflen) {
    return sysArg(BootRecord.the_boot_record.sysArgIP, argno, buf, buflen);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native int sysArg(org.vmmagic.unboxed.Address nativeIP, int argno, byte[] buf, int buflen);

  @java.lang.Override
  public int sysGetenv(byte[] varName, byte[] buf, int limit) {
    return sysGetenv(BootRecord.the_boot_record.sysGetenvIP, varName, buf, limit);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native int sysGetenv(org.vmmagic.unboxed.Address nativeIP, byte[] varName, byte[] buf, int limit);

  @java.lang.Override
  public void sysCopy(org.vmmagic.unboxed.Address dst, org.vmmagic.unboxed.Address src, org.vmmagic.unboxed.Extent cnt) {
    sysCopy(BootRecord.the_boot_record.sysCopyIP, dst, src, cnt);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysCopy(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address dst, org.vmmagic.unboxed.Address src, org.vmmagic.unboxed.Extent cnt);

  @java.lang.Override
  public void sysMemmove(org.vmmagic.unboxed.Address dst, org.vmmagic.unboxed.Address src, org.vmmagic.unboxed.Extent cnt) {
    sysMemmove(BootRecord.the_boot_record.sysMemmoveIP, dst, src, cnt);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysMemmove(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address dst, org.vmmagic.unboxed.Address src, org.vmmagic.unboxed.Extent cnt);

  @java.lang.Override
  public org.vmmagic.unboxed.Address sysMalloc(int length) {
    return sysMalloc(BootRecord.the_boot_record.sysMallocIP, length);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native org.vmmagic.unboxed.Address sysMalloc(org.vmmagic.unboxed.Address nativeIP, int length);

  @java.lang.Override
  public org.vmmagic.unboxed.Address sysCalloc(int length) {
    return sysCalloc(BootRecord.the_boot_record.sysCallocIP, length);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native org.vmmagic.unboxed.Address sysCalloc(org.vmmagic.unboxed.Address nativeIP, int length);

  @java.lang.Override
  public void sysFree(org.vmmagic.unboxed.Address location) {
    sysFree(BootRecord.the_boot_record.sysFreeIP, location);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysFree(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address location);

  @java.lang.Override
  public void sysZeroNT(org.vmmagic.unboxed.Address dst, org.vmmagic.unboxed.Extent cnt) {
    sysZeroNT(BootRecord.the_boot_record.sysZeroNTIP, dst, cnt);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysZeroNT(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address dst, org.vmmagic.unboxed.Extent cnt);

  @java.lang.Override
  public void sysZero(org.vmmagic.unboxed.Address dst, org.vmmagic.unboxed.Extent cnt) {
    sysZero(BootRecord.the_boot_record.sysZeroIP, dst, cnt);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysZero(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address dst, org.vmmagic.unboxed.Extent cnt);

  @java.lang.Override
  public void sysZeroPages(org.vmmagic.unboxed.Address dst, int cnt) {
    sysZeroPages(BootRecord.the_boot_record.sysZeroPagesIP, dst, cnt);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysZeroPages(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address dst, int cnt);

  @java.lang.Override
  public void sysSyncCache(org.vmmagic.unboxed.Address address, int size) {
    sysSyncCache(BootRecord.the_boot_record.sysSyncCacheIP, address, size);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysSyncCache(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address address, int size);

  @java.lang.Override
  public int sysPerfEventInit(int events) {
    return sysPerfEventInit(BootRecord.the_boot_record.sysPerfEventInitIP, events);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native int sysPerfEventInit(org.vmmagic.unboxed.Address nativeIP, int events);

  @java.lang.Override
  public int sysPerfEventCreate(int id, byte[] name) {
    return sysPerfEventCreate(BootRecord.the_boot_record.sysPerfEventCreateIP, id, name);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native int sysPerfEventCreate(org.vmmagic.unboxed.Address nativeIP, int id, byte[] name);

  @java.lang.Override
  public void sysPerfEventEnable() {
    sysPerfEventEnable(BootRecord.the_boot_record.sysPerfEventEnableIP);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysPerfEventEnable(org.vmmagic.unboxed.Address nativeIP);

  @java.lang.Override
  public void sysPerfEventDisable() {
    sysPerfEventDisable(BootRecord.the_boot_record.sysPerfEventDisableIP);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysPerfEventDisable(org.vmmagic.unboxed.Address nativeIP);

  @java.lang.Override
  public int sysPerfEventRead(int id, long[] values) {
    return sysPerfEventRead(BootRecord.the_boot_record.sysPerfEventReadIP, id, values);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native int sysPerfEventRead(org.vmmagic.unboxed.Address nativeIP, int id, long[] values);

  @java.lang.Override
  public int sysReadByte(int fd) {
    return sysReadByte(BootRecord.the_boot_record.sysReadByteIP, fd);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native int sysReadByte(org.vmmagic.unboxed.Address nativeIP, int fd);

  @java.lang.Override
  public int sysWriteByte(int fd, int data) {
    return sysWriteByte(BootRecord.the_boot_record.sysWriteByteIP, fd, data);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native int sysWriteByte(org.vmmagic.unboxed.Address nativeIP, int fd, int data);

  @java.lang.Override
  public int sysReadBytes(int fd, org.vmmagic.unboxed.Address buf, int cnt) {
    return sysReadBytes(BootRecord.the_boot_record.sysReadBytesIP, fd, buf, cnt);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native int sysReadBytes(org.vmmagic.unboxed.Address nativeIP, int fd, org.vmmagic.unboxed.Address buf, int cnt);

  @java.lang.Override
  public int sysWriteBytes(int fd, org.vmmagic.unboxed.Address buf, int cnt) {
    return sysWriteBytes(BootRecord.the_boot_record.sysWriteBytesIP, fd, buf, cnt);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native int sysWriteBytes(org.vmmagic.unboxed.Address nativeIP, int fd, org.vmmagic.unboxed.Address buf, int cnt);

  @java.lang.Override
  public org.vmmagic.unboxed.Address sysMMap(org.vmmagic.unboxed.Address start, org.vmmagic.unboxed.Extent length, int protection, int flags, int fd, org.vmmagic.unboxed.Offset offset) {
    return sysMMap(BootRecord.the_boot_record.sysMMapIP, start, length, protection, flags, fd, offset);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native org.vmmagic.unboxed.Address sysMMap(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address start, org.vmmagic.unboxed.Extent length, int protection, int flags, int fd, org.vmmagic.unboxed.Offset offset);

  @java.lang.Override
  public org.vmmagic.unboxed.Address sysMMapErrno(org.vmmagic.unboxed.Address start, org.vmmagic.unboxed.Extent length, int protection, int flags, int fd, org.vmmagic.unboxed.Offset offset) {
    return sysMMapErrno(BootRecord.the_boot_record.sysMMapErrnoIP, start, length, protection, flags, fd, offset);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native org.vmmagic.unboxed.Address sysMMapErrno(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address start, org.vmmagic.unboxed.Extent length, int protection, int flags, int fd, org.vmmagic.unboxed.Offset offset);

  @java.lang.Override
  public int sysMProtect(org.vmmagic.unboxed.Address start, org.vmmagic.unboxed.Extent length, int prot) {
    return sysMProtect(BootRecord.the_boot_record.sysMProtectIP, start, length, prot);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native int sysMProtect(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address start, org.vmmagic.unboxed.Extent length, int prot);

  @java.lang.Override
  public int sysNumProcessors() {
    return sysNumProcessors(BootRecord.the_boot_record.sysNumProcessorsIP);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native int sysNumProcessors(org.vmmagic.unboxed.Address nativeIP);

  @java.lang.Override
  public org.vmmagic.unboxed.Word sysThreadCreate(org.vmmagic.unboxed.Address ip, org.vmmagic.unboxed.Address fp, org.vmmagic.unboxed.Address tr, org.vmmagic.unboxed.Address jtoc) {
    return sysThreadCreate(BootRecord.the_boot_record.sysThreadCreateIP, ip, fp, tr, jtoc);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native org.vmmagic.unboxed.Word sysThreadCreate(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address ip, org.vmmagic.unboxed.Address fp, org.vmmagic.unboxed.Address tr, org.vmmagic.unboxed.Address jtoc);

  @java.lang.Override
  public int sysThreadBindSupported() {
    return sysThreadBindSupported(BootRecord.the_boot_record.sysThreadBindSupportedIP);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native int sysThreadBindSupported(org.vmmagic.unboxed.Address nativeIP);

  @java.lang.Override
  public void sysThreadBind(int cpuId) {
    sysThreadBind(BootRecord.the_boot_record.sysThreadBindIP, cpuId);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysThreadBind(org.vmmagic.unboxed.Address nativeIP, int cpuId);

  @java.lang.Override
  public void sysThreadYield() {
    sysThreadYield(BootRecord.the_boot_record.sysThreadYieldIP);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysThreadYield(org.vmmagic.unboxed.Address nativeIP);

  @java.lang.Override
  public org.vmmagic.unboxed.Word sysGetThreadId() {
    return sysGetThreadId(BootRecord.the_boot_record.sysGetThreadIdIP);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native org.vmmagic.unboxed.Word sysGetThreadId(org.vmmagic.unboxed.Address nativeIP);

  @java.lang.Override
  public org.vmmagic.unboxed.Word sysGetThreadPriorityHandle() {
    return sysGetThreadPriorityHandle(BootRecord.the_boot_record.sysGetThreadPriorityHandleIP);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native org.vmmagic.unboxed.Word sysGetThreadPriorityHandle(org.vmmagic.unboxed.Address nativeIP);

  @java.lang.Override
  public int sysGetThreadPriority(org.vmmagic.unboxed.Word thread, org.vmmagic.unboxed.Word handle) {
    return sysGetThreadPriority(BootRecord.the_boot_record.sysGetThreadPriorityIP, thread, handle);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native int sysGetThreadPriority(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Word thread, org.vmmagic.unboxed.Word handle);

  @java.lang.Override
  public int sysSetThreadPriority(org.vmmagic.unboxed.Word thread, org.vmmagic.unboxed.Word handle, int priority) {
    return sysSetThreadPriority(BootRecord.the_boot_record.sysSetThreadPriorityIP, thread, handle, priority);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native int sysSetThreadPriority(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Word thread, org.vmmagic.unboxed.Word handle, int priority);

  @java.lang.Override
  public int sysStashVMThread(org.jikesrvm.scheduler.RVMThread vmThread) {
    return sysStashVMThread(BootRecord.the_boot_record.sysStashVMThreadIP, vmThread);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native int sysStashVMThread(org.vmmagic.unboxed.Address nativeIP, org.jikesrvm.scheduler.RVMThread vmThread);

  @java.lang.Override
  public void sysThreadTerminate() {
    sysThreadTerminate(BootRecord.the_boot_record.sysThreadTerminateIP);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysThreadTerminate(org.vmmagic.unboxed.Address nativeIP);

  @java.lang.Override
  public org.vmmagic.unboxed.Word sysMonitorCreate() {
    return sysMonitorCreate(BootRecord.the_boot_record.sysMonitorCreateIP);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native org.vmmagic.unboxed.Word sysMonitorCreate(org.vmmagic.unboxed.Address nativeIP);

  @java.lang.Override
  public void sysMonitorDestroy(org.vmmagic.unboxed.Word monitor) {
    sysMonitorDestroy(BootRecord.the_boot_record.sysMonitorDestroyIP, monitor);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysMonitorDestroy(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Word monitor);

  @java.lang.Override
  public int sysMonitorEnter(org.vmmagic.unboxed.Word monitor) {
    return sysMonitorEnter(BootRecord.the_boot_record.sysMonitorEnterIP, monitor);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native int sysMonitorEnter(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Word monitor);

  @java.lang.Override
  public int sysMonitorExit(org.vmmagic.unboxed.Word monitor) {
    return sysMonitorExit(BootRecord.the_boot_record.sysMonitorExitIP, monitor);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native int sysMonitorExit(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Word monitor);

  @java.lang.Override
  public void sysMonitorTimedWaitAbsolute(org.vmmagic.unboxed.Word monitor, long whenWakeupNanos) {
    sysMonitorTimedWaitAbsolute(BootRecord.the_boot_record.sysMonitorTimedWaitAbsoluteIP, monitor, whenWakeupNanos);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysMonitorTimedWaitAbsolute(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Word monitor, long whenWakeupNanos);

  @java.lang.Override
  public void sysMonitorWait(org.vmmagic.unboxed.Word monitor) {
    sysMonitorWait(BootRecord.the_boot_record.sysMonitorWaitIP, monitor);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysMonitorWait(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Word monitor);

  @java.lang.Override
  public void sysMonitorBroadcast(org.vmmagic.unboxed.Word monitor) {
    sysMonitorBroadcast(BootRecord.the_boot_record.sysMonitorBroadcastIP, monitor);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysMonitorBroadcast(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Word monitor);

  @java.lang.Override
  public long sysLongDivide(long x, long y) {
    return sysLongDivide(BootRecord.the_boot_record.sysLongDivideIP, x, y);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native long sysLongDivide(org.vmmagic.unboxed.Address nativeIP, long x, long y);

  @java.lang.Override
  public long sysLongRemainder(long x, long y) {
    return sysLongRemainder(BootRecord.the_boot_record.sysLongRemainderIP, x, y);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native long sysLongRemainder(org.vmmagic.unboxed.Address nativeIP, long x, long y);

  @java.lang.Override
  public float sysLongToFloat(long x) {
    return sysLongToFloat(BootRecord.the_boot_record.sysLongToFloatIP, x);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native float sysLongToFloat(org.vmmagic.unboxed.Address nativeIP, long x);

  @java.lang.Override
  public double sysLongToDouble(long x) {
    return sysLongToDouble(BootRecord.the_boot_record.sysLongToDoubleIP, x);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native double sysLongToDouble(org.vmmagic.unboxed.Address nativeIP, long x);

  @java.lang.Override
  public int sysFloatToInt(float x) {
    return sysFloatToInt(BootRecord.the_boot_record.sysFloatToIntIP, x);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native int sysFloatToInt(org.vmmagic.unboxed.Address nativeIP, float x);

  @java.lang.Override
  public int sysDoubleToInt(double x) {
    return sysDoubleToInt(BootRecord.the_boot_record.sysDoubleToIntIP, x);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native int sysDoubleToInt(org.vmmagic.unboxed.Address nativeIP, double x);

  @java.lang.Override
  public long sysFloatToLong(float x) {
    return sysFloatToLong(BootRecord.the_boot_record.sysFloatToLongIP, x);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native long sysFloatToLong(org.vmmagic.unboxed.Address nativeIP, float x);

  @java.lang.Override
  public long sysDoubleToLong(double x) {
    return sysDoubleToLong(BootRecord.the_boot_record.sysDoubleToLongIP, x);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native long sysDoubleToLong(org.vmmagic.unboxed.Address nativeIP, double x);

  @java.lang.Override
  public double sysDoubleRemainder(double x, double y) {
    return sysDoubleRemainder(BootRecord.the_boot_record.sysDoubleRemainderIP, x, y);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native double sysDoubleRemainder(org.vmmagic.unboxed.Address nativeIP, double x, double y);

  @java.lang.Override
  public float sysPrimitiveParseFloat(byte[] buf) {
    return sysPrimitiveParseFloat(BootRecord.the_boot_record.sysPrimitiveParseFloatIP, buf);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native float sysPrimitiveParseFloat(org.vmmagic.unboxed.Address nativeIP, byte[] buf);

  @java.lang.Override
  public int sysPrimitiveParseInt(byte[] buf) {
    return sysPrimitiveParseInt(BootRecord.the_boot_record.sysPrimitiveParseIntIP, buf);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native int sysPrimitiveParseInt(org.vmmagic.unboxed.Address nativeIP, byte[] buf);

  @java.lang.Override
  public long sysPrimitiveParseLong(byte[] buf) {
    return sysPrimitiveParseLong(BootRecord.the_boot_record.sysPrimitiveParseLongIP, buf);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native long sysPrimitiveParseLong(org.vmmagic.unboxed.Address nativeIP, byte[] buf);

  @java.lang.Override
  public long sysParseMemorySize(byte[] sizeName, byte[] sizeFlag, byte[] defaultFactor, int roundTo, byte[] argToken, byte[] subArg) {
    return sysParseMemorySize(BootRecord.the_boot_record.sysParseMemorySizeIP, sizeName, sizeFlag, defaultFactor, roundTo, argToken, subArg);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native long sysParseMemorySize(org.vmmagic.unboxed.Address nativeIP, byte[] sizeName, byte[] sizeFlag, byte[] defaultFactor, int roundTo, byte[] argToken, byte[] subArg);

  @java.lang.Override
  public long sysCurrentTimeMillis() {
    return sysCurrentTimeMillis(BootRecord.the_boot_record.sysCurrentTimeMillisIP);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native long sysCurrentTimeMillis(org.vmmagic.unboxed.Address nativeIP);

  @java.lang.Override
  public long sysNanoTime() {
    return sysNanoTime(BootRecord.the_boot_record.sysNanoTimeIP);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native long sysNanoTime(org.vmmagic.unboxed.Address nativeIP);

  @java.lang.Override
  public void sysNanoSleep(long howLongNanos) {
    sysNanoSleep(BootRecord.the_boot_record.sysNanoSleepIP, howLongNanos);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysNanoSleep(org.vmmagic.unboxed.Address nativeIP, long howLongNanos);

  @java.lang.Override
  public org.vmmagic.unboxed.Address sysDlopen(byte[] libname) {
    return sysDlopen(BootRecord.the_boot_record.sysDlopenIP, libname);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native org.vmmagic.unboxed.Address sysDlopen(org.vmmagic.unboxed.Address nativeIP, byte[] libname);

  @java.lang.Override
  public org.vmmagic.unboxed.Address sysDlsym(org.vmmagic.unboxed.Address libHandler, byte[] symbolName) {
    return sysDlsym(BootRecord.the_boot_record.sysDlsymIP, libHandler, symbolName);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native org.vmmagic.unboxed.Address sysDlsym(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address libHandler, byte[] symbolName);

  @java.lang.Override
  public org.vmmagic.unboxed.Address sysVaCopy(org.vmmagic.unboxed.Address va_list) {
    return sysVaCopy(BootRecord.the_boot_record.sysVaCopyIP, va_list);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native org.vmmagic.unboxed.Address sysVaCopy(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address va_list);

  @java.lang.Override
  public void sysVaEnd(org.vmmagic.unboxed.Address va_list) {
    sysVaEnd(BootRecord.the_boot_record.sysVaEndIP, va_list);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysVaEnd(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address va_list);

  @java.lang.Override
  public boolean sysVaArgJboolean(org.vmmagic.unboxed.Address va_list) {
    return sysVaArgJboolean(BootRecord.the_boot_record.sysVaArgJbooleanIP, va_list);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native boolean sysVaArgJboolean(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address va_list);

  @java.lang.Override
  public byte sysVaArgJbyte(org.vmmagic.unboxed.Address va_list) {
    return sysVaArgJbyte(BootRecord.the_boot_record.sysVaArgJbyteIP, va_list);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native byte sysVaArgJbyte(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address va_list);

  @java.lang.Override
  public char sysVaArgJchar(org.vmmagic.unboxed.Address va_list) {
    return sysVaArgJchar(BootRecord.the_boot_record.sysVaArgJcharIP, va_list);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native char sysVaArgJchar(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address va_list);

  @java.lang.Override
  public short sysVaArgJshort(org.vmmagic.unboxed.Address va_list) {
    return sysVaArgJshort(BootRecord.the_boot_record.sysVaArgJshortIP, va_list);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native short sysVaArgJshort(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address va_list);

  @java.lang.Override
  public int sysVaArgJint(org.vmmagic.unboxed.Address va_list) {
    return sysVaArgJint(BootRecord.the_boot_record.sysVaArgJintIP, va_list);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native int sysVaArgJint(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address va_list);

  @java.lang.Override
  public long sysVaArgJlong(org.vmmagic.unboxed.Address va_list) {
    return sysVaArgJlong(BootRecord.the_boot_record.sysVaArgJlongIP, va_list);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native long sysVaArgJlong(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address va_list);

  @java.lang.Override
  public float sysVaArgJfloat(org.vmmagic.unboxed.Address va_list) {
    return sysVaArgJfloat(BootRecord.the_boot_record.sysVaArgJfloatIP, va_list);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native float sysVaArgJfloat(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address va_list);

  @java.lang.Override
  public double sysVaArgJdouble(org.vmmagic.unboxed.Address va_list) {
    return sysVaArgJdouble(BootRecord.the_boot_record.sysVaArgJdoubleIP, va_list);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native double sysVaArgJdouble(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address va_list);

  @java.lang.Override
  public int sysVaArgJobject(org.vmmagic.unboxed.Address va_list) {
    return sysVaArgJobject(BootRecord.the_boot_record.sysVaArgJobjectIP, va_list);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native int sysVaArgJobject(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address va_list);

  @java.lang.Override
  public void sysEnableAlignmentChecking() {
    sysEnableAlignmentChecking(BootRecord.the_boot_record.sysEnableAlignmentCheckingIP);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysEnableAlignmentChecking(org.vmmagic.unboxed.Address nativeIP);

  @java.lang.Override
  public void sysDisableAlignmentChecking() {
    sysDisableAlignmentChecking(BootRecord.the_boot_record.sysDisableAlignmentCheckingIP);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysDisableAlignmentChecking(org.vmmagic.unboxed.Address nativeIP);

  @java.lang.Override
  public void sysReportAlignmentChecking() {
    sysReportAlignmentChecking(BootRecord.the_boot_record.sysReportAlignmentCheckingIP);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysReportAlignmentChecking(org.vmmagic.unboxed.Address nativeIP);

  @java.lang.Override
  public org.vmmagic.unboxed.Address gcspyDriverAddStream(org.vmmagic.unboxed.Address driver, int id) {
    return gcspyDriverAddStream(BootRecord.the_boot_record.gcspyDriverAddStreamIP, driver, id);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native org.vmmagic.unboxed.Address gcspyDriverAddStream(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address driver, int id);

  @java.lang.Override
  public void gcspyDriverEndOutput(org.vmmagic.unboxed.Address driver) {
    gcspyDriverEndOutput(BootRecord.the_boot_record.gcspyDriverEndOutputIP, driver);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void gcspyDriverEndOutput(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address driver);

  @java.lang.Override
  public void gcspyDriverInit(org.vmmagic.unboxed.Address driver, int id, org.vmmagic.unboxed.Address serverName, org.vmmagic.unboxed.Address driverName, org.vmmagic.unboxed.Address title, org.vmmagic.unboxed.Address blockInfo, int tileNum, org.vmmagic.unboxed.Address unused, int mainSpace) {
    gcspyDriverInit(BootRecord.the_boot_record.gcspyDriverInitIP, driver, id, serverName, driverName, title, blockInfo, tileNum, unused, mainSpace);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void gcspyDriverInit(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address driver, int id, org.vmmagic.unboxed.Address serverName, org.vmmagic.unboxed.Address driverName, org.vmmagic.unboxed.Address title, org.vmmagic.unboxed.Address blockInfo, int tileNum, org.vmmagic.unboxed.Address unused, int mainSpace);

  @java.lang.Override
  public void gcspyDriverInitOutput(org.vmmagic.unboxed.Address driver) {
    gcspyDriverInitOutput(BootRecord.the_boot_record.gcspyDriverInitOutputIP, driver);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void gcspyDriverInitOutput(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address driver);

  @java.lang.Override
  public void gcspyDriverResize(org.vmmagic.unboxed.Address driver, int size) {
    gcspyDriverResize(BootRecord.the_boot_record.gcspyDriverResizeIP, driver, size);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void gcspyDriverResize(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address driver, int size);

  @java.lang.Override
  public void gcspyDriverSetTileNameRange(org.vmmagic.unboxed.Address driver, int i, org.vmmagic.unboxed.Address start, org.vmmagic.unboxed.Address end) {
    gcspyDriverSetTileNameRange(BootRecord.the_boot_record.gcspyDriverSetTileNameRangeIP, driver, i, start, end);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void gcspyDriverSetTileNameRange(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address driver, int i, org.vmmagic.unboxed.Address start, org.vmmagic.unboxed.Address end);

  @java.lang.Override
  public void gcspyDriverSetTileName(org.vmmagic.unboxed.Address driver, int i, org.vmmagic.unboxed.Address start, long value) {
    gcspyDriverSetTileName(BootRecord.the_boot_record.gcspyDriverSetTileNameIP, driver, i, start, value);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void gcspyDriverSetTileName(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address driver, int i, org.vmmagic.unboxed.Address start, long value);

  @java.lang.Override
  public void gcspyDriverSpaceInfo(org.vmmagic.unboxed.Address driver, org.vmmagic.unboxed.Address info) {
    gcspyDriverSpaceInfo(BootRecord.the_boot_record.gcspyDriverSpaceInfoIP, driver, info);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void gcspyDriverSpaceInfo(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address driver, org.vmmagic.unboxed.Address info);

  @java.lang.Override
  public void gcspyDriverStartComm(org.vmmagic.unboxed.Address driver) {
    gcspyDriverStartComm(BootRecord.the_boot_record.gcspyDriverStartCommIP, driver);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void gcspyDriverStartComm(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address driver);

  @java.lang.Override
  public void gcspyDriverStream(org.vmmagic.unboxed.Address driver, int id, int len) {
    gcspyDriverStream(BootRecord.the_boot_record.gcspyDriverStreamIP, driver, id, len);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void gcspyDriverStream(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address driver, int id, int len);

  @java.lang.Override
  public void gcspyDriverStreamByteValue(org.vmmagic.unboxed.Address driver, byte value) {
    gcspyDriverStreamByteValue(BootRecord.the_boot_record.gcspyDriverStreamByteValueIP, driver, value);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void gcspyDriverStreamByteValue(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address driver, byte value);

  @java.lang.Override
  public void gcspyDriverStreamShortValue(org.vmmagic.unboxed.Address driver, short value) {
    gcspyDriverStreamShortValue(BootRecord.the_boot_record.gcspyDriverStreamShortValueIP, driver, value);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void gcspyDriverStreamShortValue(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address driver, short value);

  @java.lang.Override
  public void gcspyDriverStreamIntValue(org.vmmagic.unboxed.Address driver, int value) {
    gcspyDriverStreamIntValue(BootRecord.the_boot_record.gcspyDriverStreamIntValueIP, driver, value);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void gcspyDriverStreamIntValue(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address driver, int value);

  @java.lang.Override
  public void gcspyDriverSummary(org.vmmagic.unboxed.Address driver, int id, int len) {
    gcspyDriverSummary(BootRecord.the_boot_record.gcspyDriverSummaryIP, driver, id, len);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void gcspyDriverSummary(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address driver, int id, int len);

  @java.lang.Override
  public void gcspyDriverSummaryValue(org.vmmagic.unboxed.Address driver, int value) {
    gcspyDriverSummaryValue(BootRecord.the_boot_record.gcspyDriverSummaryValueIP, driver, value);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void gcspyDriverSummaryValue(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address driver, int value);

  @java.lang.Override
  public void gcspyIntWriteControl(org.vmmagic.unboxed.Address driver, int id, int tileNum) {
    gcspyIntWriteControl(BootRecord.the_boot_record.gcspyIntWriteControlIP, driver, id, tileNum);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void gcspyIntWriteControl(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address driver, int id, int tileNum);

  @java.lang.Override
  public org.vmmagic.unboxed.Address gcspyMainServerAddDriver(org.vmmagic.unboxed.Address addr) {
    return gcspyMainServerAddDriver(BootRecord.the_boot_record.gcspyMainServerAddDriverIP, addr);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native org.vmmagic.unboxed.Address gcspyMainServerAddDriver(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address addr);

  @java.lang.Override
  public void gcspyMainServerAddEvent(org.vmmagic.unboxed.Address server, int event, org.vmmagic.unboxed.Address name) {
    gcspyMainServerAddEvent(BootRecord.the_boot_record.gcspyMainServerAddEventIP, server, event, name);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void gcspyMainServerAddEvent(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address server, int event, org.vmmagic.unboxed.Address name);

  @java.lang.Override
  public org.vmmagic.unboxed.Address gcspyMainServerInit(int port, int len, org.vmmagic.unboxed.Address name, int verbose) {
    return gcspyMainServerInit(BootRecord.the_boot_record.gcspyMainServerInitIP, port, len, name, verbose);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native org.vmmagic.unboxed.Address gcspyMainServerInit(org.vmmagic.unboxed.Address nativeIP, int port, int len, org.vmmagic.unboxed.Address name, int verbose);

  @java.lang.Override
  public int gcspyMainServerIsConnected(org.vmmagic.unboxed.Address server, int event) {
    return gcspyMainServerIsConnected(BootRecord.the_boot_record.gcspyMainServerIsConnectedIP, server, event);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native int gcspyMainServerIsConnected(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address server, int event);

  @java.lang.Override
  public org.vmmagic.unboxed.Address gcspyMainServerOuterLoop() {
    return gcspyMainServerOuterLoop(BootRecord.the_boot_record.gcspyMainServerOuterLoopIP);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native org.vmmagic.unboxed.Address gcspyMainServerOuterLoop(org.vmmagic.unboxed.Address nativeIP);

  @java.lang.Override
  public void gcspyMainServerSafepoint(org.vmmagic.unboxed.Address server, int event) {
    gcspyMainServerSafepoint(BootRecord.the_boot_record.gcspyMainServerSafepointIP, server, event);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void gcspyMainServerSafepoint(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address server, int event);

  @java.lang.Override
  public void gcspyMainServerSetGeneralInfo(org.vmmagic.unboxed.Address server, org.vmmagic.unboxed.Address info) {
    gcspyMainServerSetGeneralInfo(BootRecord.the_boot_record.gcspyMainServerSetGeneralInfoIP, server, info);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void gcspyMainServerSetGeneralInfo(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address server, org.vmmagic.unboxed.Address info);

  @java.lang.Override
  public void gcspyMainServerStartCompensationTimer(org.vmmagic.unboxed.Address server) {
    gcspyMainServerStartCompensationTimer(BootRecord.the_boot_record.gcspyMainServerStartCompensationTimerIP, server);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void gcspyMainServerStartCompensationTimer(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address server);

  @java.lang.Override
  public void gcspyMainServerStopCompensationTimer(org.vmmagic.unboxed.Address server) {
    gcspyMainServerStopCompensationTimer(BootRecord.the_boot_record.gcspyMainServerStopCompensationTimerIP, server);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void gcspyMainServerStopCompensationTimer(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address server);

  @java.lang.Override
  public void gcspyStartserver(org.vmmagic.unboxed.Address server, int wait, org.vmmagic.unboxed.Address serverOuterLoop) {
    gcspyStartserver(BootRecord.the_boot_record.gcspyStartserverIP, server, wait, serverOuterLoop);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void gcspyStartserver(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address server, int wait, org.vmmagic.unboxed.Address serverOuterLoop);

  @java.lang.Override
  public void gcspyStreamInit(org.vmmagic.unboxed.Address stream, int id, int dataType, org.vmmagic.unboxed.Address name, int minValue, int maxValue, int zeroValue, int defaultValue, org.vmmagic.unboxed.Address pre, org.vmmagic.unboxed.Address post, int presentation, int paintStyle, int maxStreamIndex, int red, int green, int blue) {
    gcspyStreamInit(BootRecord.the_boot_record.gcspyStreamInitIP, stream, id, dataType, name, minValue, maxValue, zeroValue, defaultValue, pre, post, presentation, paintStyle, maxStreamIndex, red, green, blue);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void gcspyStreamInit(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address stream, int id, int dataType, org.vmmagic.unboxed.Address name, int minValue, int maxValue, int zeroValue, int defaultValue, org.vmmagic.unboxed.Address pre, org.vmmagic.unboxed.Address post, int presentation, int paintStyle, int maxStreamIndex, int red, int green, int blue);

  @java.lang.Override
  public void gcspyFormatSize(org.vmmagic.unboxed.Address buffer, int size) {
    gcspyFormatSize(BootRecord.the_boot_record.gcspyFormatSizeIP, buffer, size);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void gcspyFormatSize(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address buffer, int size);

  @java.lang.Override
  public int gcspySprintf(org.vmmagic.unboxed.Address str, org.vmmagic.unboxed.Address format, org.vmmagic.unboxed.Address value) {
    return gcspySprintf(BootRecord.the_boot_record.gcspySprintfIP, str, format, value);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native int gcspySprintf(org.vmmagic.unboxed.Address nativeIP, org.vmmagic.unboxed.Address str, org.vmmagic.unboxed.Address format, org.vmmagic.unboxed.Address value);

  @java.lang.Override
  public void sysStackAlignmentTest() {
    sysStackAlignmentTest(BootRecord.the_boot_record.sysStackAlignmentTestIP);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysStackAlignmentTest(org.vmmagic.unboxed.Address nativeIP);

  @java.lang.Override
  public void sysArgumentPassingTest(long firstLong, long secondLong, long thirdLong, long fourthLong, long fifthLong, long sixthLong, long seventhLong, long eightLong, double firstDouble, double secondDouble, double thirdDouble, double fourthDouble, double fifthDouble, double sixthDouble, double seventhDouble, double eightDouble, int firstInt, long ninthLong, byte[] firstByteArray, double ninthDouble, org.vmmagic.unboxed.Address firstAddress) {
    sysArgumentPassingTest(BootRecord.the_boot_record.sysArgumentPassingTestIP, firstLong, secondLong, thirdLong, fourthLong, fifthLong, sixthLong, seventhLong, eightLong, firstDouble, secondDouble, thirdDouble, fourthDouble, fifthDouble, sixthDouble, seventhDouble, eightDouble, firstInt, ninthLong, firstByteArray, ninthDouble, firstAddress);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysArgumentPassingTest(org.vmmagic.unboxed.Address nativeIP, long firstLong, long secondLong, long thirdLong, long fourthLong, long fifthLong, long sixthLong, long seventhLong, long eightLong, double firstDouble, double secondDouble, double thirdDouble, double fourthDouble, double fifthDouble, double sixthDouble, double seventhDouble, double eightDouble, int firstInt, long ninthLong, byte[] firstByteArray, double ninthDouble, org.vmmagic.unboxed.Address firstAddress);

  @java.lang.Override
  public void sysArgumentPassingSeveralLongsAndSeveralDoubles(long firstLong, long secondLong, long thirdLong, long fourthLong, long fifthLong, long sixthLong, long seventhLong, long eightLong, double firstDouble, double secondDouble, double thirdDouble, double fourthDouble, double fifthDouble, double sixthDouble, double seventhDouble, double eightDouble) {
    sysArgumentPassingSeveralLongsAndSeveralDoubles(BootRecord.the_boot_record.sysArgumentPassingSeveralLongsAndSeveralDoublesIP, firstLong, secondLong, thirdLong, fourthLong, fifthLong, sixthLong, seventhLong, eightLong, firstDouble, secondDouble, thirdDouble, fourthDouble, fifthDouble, sixthDouble, seventhDouble, eightDouble);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysArgumentPassingSeveralLongsAndSeveralDoubles(org.vmmagic.unboxed.Address nativeIP, long firstLong, long secondLong, long thirdLong, long fourthLong, long fifthLong, long sixthLong, long seventhLong, long eightLong, double firstDouble, double secondDouble, double thirdDouble, double fourthDouble, double fifthDouble, double sixthDouble, double seventhDouble, double eightDouble);

  @java.lang.Override
  public void sysArgumentPassingSeveralFloatsAndSeveralInts(float firstFloat, float secondFloat, float thirdFloat, float fourthFloat, float fifthFloat, float sixthFloat, float seventhFloat, float eightFloat, int firstInt, int secondInt, int thirdInt, int fourthInt, int fifthInt, int sixthInt, int seventhInt, int eightInt) {
    sysArgumentPassingSeveralFloatsAndSeveralInts(BootRecord.the_boot_record.sysArgumentPassingSeveralFloatsAndSeveralIntsIP, firstFloat, secondFloat, thirdFloat, fourthFloat, fifthFloat, sixthFloat, seventhFloat, eightFloat, firstInt, secondInt, thirdInt, fourthInt, fifthInt, sixthInt, seventhInt, eightInt);
  }

  @org.vmmagic.pragma.SysCallNative
  private static native void sysArgumentPassingSeveralFloatsAndSeveralInts(org.vmmagic.unboxed.Address nativeIP, float firstFloat, float secondFloat, float thirdFloat, float fourthFloat, float fifthFloat, float sixthFloat, float seventhFloat, float eightFloat, int firstInt, int secondInt, int thirdInt, int fourthInt, int fifthInt, int sixthInt, int seventhInt, int eightInt);

}