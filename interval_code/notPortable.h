/* based in part on Sam Ferguson's macros.h */

#ifndef notPortableH
#define notPortableH

#define DA_SYSTEM 3


#if DA_SYSTEM == 1 /* PPC, PowerMac */

#define ROUND_UP        fesetround(FE_UPWARD)
#define ROUND_DOWN      fesetround(FE_DOWNWARD)
#define ROUND_NEAR      fesetround(FE_TONEAREST)
#define ROUND_ZERO      fesetround(FE_TOWARDZERO)
#define ISNAN( x )      isnan( x )

#elif DA_SYSTEM == 2    /* Sparc */

#include <float.h>
#include <stdlib.h>
#include <ieeefp.h>

#define ROUND_UP        ieee_flags("set","direction","positive",0);
#define ROUND_DOWN      ieee_flags("set","direction","negative",0);
#define ROUND_NEAR      ieee_flags("set","direction","nearest",0);
#define ROUND_ZERO      ieee_flags("set","direction","tozero",0);
#define ISNAN( x )      isnan( x )

#elif DA_SYSTEM == 3    /* SGI, Solaris */

#include <float.h>
#include <stdlib.h>
#include <ieeefp.h>

#define ROUND_UP        fpsetround( FP_RP )
#define ROUND_DOWN      fpsetround( FP_RM )
#define ROUND_NEAR      fpsetround( FP_RN )
#define ROUND_ZERO      fpsetround( FP_RZ )
#define ISNAN( x )      isnand( x )

#else                   /* default */

#define ROUND_UP        fpsetround( FP_RP )
#define ROUND_DOWN      fpsetround( FP_RM )
#define ROUND_NEAR      fpsetround( FP_RN )
#define ROUND_ZERO      fpsetround( FP_RZ )
#define ISNAN( x )      isnand( x )

#endif


#endif
