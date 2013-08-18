const Function Lib::num2 = 
  (-2048)*Function::mk_monomial(0,0,1,0,0,3) + 6144*Function::mk_monomial(0,0,1,0,1,2) - 6144*Function::mk_monomial(0,0,1,0,2,1) + 
   2048*Function::mk_monomial(0,0,1,0,3,0) + 10240*Function::mk_monomial(0,0,1,1,0,2) + 128*Function::mk_monomial(0,0,1,1,0,3) - 
   4096*Function::mk_monomial(0,0,1,1,1,1) - 1664*Function::mk_monomial(0,0,1,1,1,2) - 6144*Function::mk_monomial(0,0,1,1,2,0) + 
   1920*Function::mk_monomial(0,0,1,1,2,1) - 384*Function::mk_monomial(0,0,1,1,3,0) - 6144*Function::mk_monomial(0,0,1,2,0,1) - 
   896*Function::mk_monomial(0,0,1,2,0,2) - 16*Function::mk_monomial(0,0,1,2,0,3) + 6144*Function::mk_monomial(0,0,1,2,1,0) - 
   256*Function::mk_monomial(0,0,1,2,1,1) + 160*Function::mk_monomial(0,0,1,2,1,2) + 1152*Function::mk_monomial(0,0,1,2,2,0) - 
   144*Function::mk_monomial(0,0,1,2,2,1) - 2048*Function::mk_monomial(0,0,1,3,0,0) + 384*Function::mk_monomial(0,0,1,3,0,1) + 
   64*Function::mk_monomial(0,0,1,3,0,2) - 1152*Function::mk_monomial(0,0,1,3,1,0) + 128*Function::mk_monomial(0,0,1,3,1,1) - 
   8*Function::mk_monomial(0,0,1,3,1,2) + 384*Function::mk_monomial(0,0,1,4,0,0) - 48*Function::mk_monomial(0,0,1,4,0,1) + 
   2048*Function::mk_monomial(0,1,0,0,0,3) - 6144*Function::mk_monomial(0,1,0,0,1,2) + 6144*Function::mk_monomial(0,1,0,0,2,1) - 
   2048*Function::mk_monomial(0,1,0,0,3,0) - 6144*Function::mk_monomial(0,1,0,1,0,2) - 384*Function::mk_monomial(0,1,0,1,0,3) - 
   4096*Function::mk_monomial(0,1,0,1,1,1) + 1920*Function::mk_monomial(0,1,0,1,1,2) + 10240*Function::mk_monomial(0,1,0,1,2,0) - 
   1664*Function::mk_monomial(0,1,0,1,2,1) + 128*Function::mk_monomial(0,1,0,1,3,0) + 6144*Function::mk_monomial(0,1,0,2,0,1) + 
   1152*Function::mk_monomial(0,1,0,2,0,2) - 6144*Function::mk_monomial(0,1,0,2,1,0) - 256*Function::mk_monomial(0,1,0,2,1,1) - 
   144*Function::mk_monomial(0,1,0,2,1,2) - 896*Function::mk_monomial(0,1,0,2,2,0) + 160*Function::mk_monomial(0,1,0,2,2,1) - 
   16*Function::mk_monomial(0,1,0,2,3,0) - 2048*Function::mk_monomial(0,1,0,3,0,0) - 1152*Function::mk_monomial(0,1,0,3,0,1) + 
   384*Function::mk_monomial(0,1,0,3,1,0) + 128*Function::mk_monomial(0,1,0,3,1,1) + 64*Function::mk_monomial(0,1,0,3,2,0) - 
   8*Function::mk_monomial(0,1,0,3,2,1) + 384*Function::mk_monomial(0,1,0,4,0,0) - 48*Function::mk_monomial(0,1,0,4,1,0) - 
   4096*Function::mk_monomial(1,0,0,1,0,2) + 8192*Function::mk_monomial(1,0,0,1,1,1) - 4096*Function::mk_monomial(1,0,0,1,2,0) + 
   512*Function::mk_monomial(1,0,0,2,0,2) - 1024*Function::mk_monomial(1,0,0,2,1,1) + 512*Function::mk_monomial(1,0,0,2,2,0) + 
   4096*Function::mk_monomial(1,0,0,3,0,0) - 16*Function::mk_monomial(1,0,0,3,0,2) + 32*Function::mk_monomial(1,0,0,3,1,1) - 
16*Function::mk_monomial(1,0,0,3,2,0) - 512*Function::mk_monomial(1,0,0,4,0,0) + 16*Function::mk_monomial(1,0,0,5,0,0);

static const interval t25("25");
const Function Lib::num_combo1 = 
(512*Function::mk_monomial(0,0,1,0,0,3) - 1536*Function::mk_monomial(0,0,1,0,1,2) + 1536*Function::mk_monomial(0,0,1,0,2,1) - 
   512*Function::mk_monomial(0,0,1,0,3,0) - 2560*Function::mk_monomial(0,0,1,1,0,2) - 32*Function::mk_monomial(0,0,1,1,0,3) + 
   1024*Function::mk_monomial(0,0,1,1,1,1) + 416*Function::mk_monomial(0,0,1,1,1,2) + 1536*Function::mk_monomial(0,0,1,1,2,0) - 
   480*Function::mk_monomial(0,0,1,1,2,1) + 96*Function::mk_monomial(0,0,1,1,3,0) + 1536*Function::mk_monomial(0,0,1,2,0,1) + 
   224*Function::mk_monomial(0,0,1,2,0,2) + 4*Function::mk_monomial(0,0,1,2,0,3) - 1536*Function::mk_monomial(0,0,1,2,1,0) + 
   64*Function::mk_monomial(0,0,1,2,1,1) - 40*Function::mk_monomial(0,0,1,2,1,2) - 288*Function::mk_monomial(0,0,1,2,2,0) + 
   36*Function::mk_monomial(0,0,1,2,2,1) + 512*Function::mk_monomial(0,0,1,3,0,0) - 96*Function::mk_monomial(0,0,1,3,0,1) - 
   16*Function::mk_monomial(0,0,1,3,0,2) + 288*Function::mk_monomial(0,0,1,3,1,0) - 32*Function::mk_monomial(0,0,1,3,1,1) + 
   2*Function::mk_monomial(0,0,1,3,1,2) - 96*Function::mk_monomial(0,0,1,4,0,0) + 12*Function::mk_monomial(0,0,1,4,0,1) + 
   25600*Function::mk_monomial(0,0,2,0,0,2) - 51200*Function::mk_monomial(0,0,2,0,1,1) + 25600*Function::mk_monomial(0,0,2,0,2,0) + 
   51200*Function::mk_monomial(0,0,2,1,0,1) - 6400*Function::mk_monomial(0,0,2,1,0,2) - 51200*Function::mk_monomial(0,0,2,1,1,0) + 
   6400*Function::mk_monomial(0,0,2,1,1,1) + 25600*Function::mk_monomial(0,0,2,2,0,0) - 6400*Function::mk_monomial(0,0,2,2,0,1) + 
   400*Function::mk_monomial(0,0,2,2,0,2) - 512*Function::mk_monomial(0,1,0,0,0,3) + 1536*Function::mk_monomial(0,1,0,0,1,2) - 
   1536*Function::mk_monomial(0,1,0,0,2,1) + 512*Function::mk_monomial(0,1,0,0,3,0) + 1536*Function::mk_monomial(0,1,0,1,0,2) + 
   96*Function::mk_monomial(0,1,0,1,0,3) + 1024*Function::mk_monomial(0,1,0,1,1,1) - 480*Function::mk_monomial(0,1,0,1,1,2) - 
   2560*Function::mk_monomial(0,1,0,1,2,0) + 416*Function::mk_monomial(0,1,0,1,2,1) - 32*Function::mk_monomial(0,1,0,1,3,0) - 
   1536*Function::mk_monomial(0,1,0,2,0,1) - 288*Function::mk_monomial(0,1,0,2,0,2) + 1536*Function::mk_monomial(0,1,0,2,1,0) + 
   64*Function::mk_monomial(0,1,0,2,1,1) + 36*Function::mk_monomial(0,1,0,2,1,2) + 224*Function::mk_monomial(0,1,0,2,2,0) - 
   40*Function::mk_monomial(0,1,0,2,2,1) + 4*Function::mk_monomial(0,1,0,2,3,0) + 512*Function::mk_monomial(0,1,0,3,0,0) + 
   288*Function::mk_monomial(0,1,0,3,0,1) - 96*Function::mk_monomial(0,1,0,3,1,0) - 32*Function::mk_monomial(0,1,0,3,1,1) - 
   16*Function::mk_monomial(0,1,0,3,2,0) + 2*Function::mk_monomial(0,1,0,3,2,1) - 96*Function::mk_monomial(0,1,0,4,0,0) + 
   12*Function::mk_monomial(0,1,0,4,1,0) - 51200*Function::mk_monomial(0,1,1,0,0,2) + 102400*Function::mk_monomial(0,1,1,0,1,1) - 
   51200*Function::mk_monomial(0,1,1,0,2,0) + 6400*Function::mk_monomial(0,1,1,1,0,2) - 12800*Function::mk_monomial(0,1,1,1,1,1) + 
   6400*Function::mk_monomial(0,1,1,1,2,0) + 51200*Function::mk_monomial(0,1,1,2,0,0) - 6400*Function::mk_monomial(0,1,1,2,0,1) - 
   6400*Function::mk_monomial(0,1,1,2,1,0) + 800*Function::mk_monomial(0,1,1,2,1,1) + 25600*Function::mk_monomial(0,2,0,0,0,2) - 
   51200*Function::mk_monomial(0,2,0,0,1,1) + 25600*Function::mk_monomial(0,2,0,0,2,0) - 51200*Function::mk_monomial(0,2,0,1,0,1) + 
   51200*Function::mk_monomial(0,2,0,1,1,0) + 6400*Function::mk_monomial(0,2,0,1,1,1) - 6400*Function::mk_monomial(0,2,0,1,2,0) + 
   25600*Function::mk_monomial(0,2,0,2,0,0) - 6400*Function::mk_monomial(0,2,0,2,1,0) + 400*Function::mk_monomial(0,2,0,2,2,0) + 
   1024*Function::mk_monomial(1,0,0,1,0,2) - 2048*Function::mk_monomial(1,0,0,1,1,1) + 1024*Function::mk_monomial(1,0,0,1,2,0) - 
   128*Function::mk_monomial(1,0,0,2,0,2) + 256*Function::mk_monomial(1,0,0,2,1,1) - 128*Function::mk_monomial(1,0,0,2,2,0) - 
   1024*Function::mk_monomial(1,0,0,3,0,0) + 4*Function::mk_monomial(1,0,0,3,0,2) - 8*Function::mk_monomial(1,0,0,3,1,1) + 
   4*Function::mk_monomial(1,0,0,3,2,0) + 128*Function::mk_monomial(1,0,0,4,0,0) - 4*Function::mk_monomial(1,0,0,5,0,0) - 
   102400*Function::mk_monomial(1,0,1,1,0,1) + 102400*Function::mk_monomial(1,0,1,1,1,0) - 
   102400*Function::mk_monomial(1,0,1,2,0,0) + 19200*Function::mk_monomial(1,0,1,2,0,1) - 6400*Function::mk_monomial(1,0,1,2,1,0) + 
   6400*Function::mk_monomial(1,0,1,3,0,0) - 800*Function::mk_monomial(1,0,1,3,0,1) + 102400*Function::mk_monomial(1,1,0,1,0,1) - 
   102400*Function::mk_monomial(1,1,0,1,1,0) - 102400*Function::mk_monomial(1,1,0,2,0,0) - 6400*Function::mk_monomial(1,1,0,2,0,1) + 
   19200*Function::mk_monomial(1,1,0,2,1,0) + 6400*Function::mk_monomial(1,1,0,3,0,0) - 800*Function::mk_monomial(1,1,0,3,1,0) + 
 102400*Function::mk_monomial(2,0,0,2,0,0) - 12800*Function::mk_monomial(2,0,0,3,0,0) + 400*Function::mk_monomial(2,0,0,4,0,0))*(L::one/t25);
