#ifdef C2NIM
  #def CUFFTAPI

  #dynlib libName
  #private libName
  #cdecl
  #if defined(windows)
  #  stdcall
  #  define libName "cufft.dll"
  #elif defined(macosx)
  #  define libName "libcufft.dylib"
  #else
  #  define libName "libcufft.so"
  #endif

  #include "cuComplex.h"
  #include "library_types.h"
  #include "driver_types.h"
  #skipinclude
#endif
