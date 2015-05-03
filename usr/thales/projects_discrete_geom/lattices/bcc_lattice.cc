
/***************************************************
 ** CODE for bcc_lattice.hl (not part of Flyspeck)
 ***************************************************/

const interval bcc_value = "5.31473969997195717";

interval selling_volume2_wide (interval p01,interval p02,interval p03,
			  interval p12, interval p13, interval p23) {
return  p01*p02*p03 + p01*p03*p12 + p02*p03*p12 +
  p01*p02*p13 + p02*p03*p13 + 
  p01*p12*p13 + p02*p12*p13 + p03*p12*p13 + 
  p01*p02*p23 + p01*p03*p23 + 
  p01*p12*p23 + p02*p12*p23 + p03*p12*p23 + 
    p01*p13*p23 + p02*p13*p23 + p03*p13*p23;
}


interval selling_surface_num_wide(interval  p01,interval p02,interval p03,
			  interval p12, interval p13, interval p23) {
  interval  p0_123 = p01 + p02 + p03;
  interval  p1_023 = p01 + p12 + p13;
  interval  p2_013 = p02 + p12 + p23;
  interval  p3_012 = p03 + p13 + p23;
  interval  p01_23 = p02 + p03 + p12 + p13;
  interval  p02_13 = p01 + p03 + p12 + p23;
  interval  p03_12 = p01 + p02 + p13 + p23;
  interval  F01_23 = p01 * p23 * interMath::sqrt(p01_23);
  interval  F02_13 = p02 * p13 * interMath::sqrt(p02_13);
  interval  F03_12 = p03 * p12 * interMath::sqrt(p03_12);
  interval  F0_123 = (p12*p13+p12*p23+p13*p23)*interMath::sqrt(p0_123);
  interval  F1_023 = (p02*p03+p02*p23+p03*p23)*interMath::sqrt(p1_023);
  interval  F2_013 = (p01*p03+p01*p13+p03*p13)*interMath::sqrt(p2_013);
  interval  F3_012 = (p01*p02+p01*p12+p02*p12)*interMath::sqrt(p3_012);
   return two*(F01_23+F02_13+F03_12+F0_123+F1_023+F2_013+F3_012);;
}

interval selling_surface_nn_wide(interval  p01,interval p02,interval p03,
			  interval p12, interval p13, interval p23) {
  return selling_surface_num_wide(p01,p02,p03,p12,p13,p23) - bcc_value;
}

static interval o1 = "0.1";
interval sqrt01(interval t) {
  return  t* interMath::sqrt(o1) / (o1);
}

interval selling_surface_num2_013_approx_wide(interval  p01,interval p02,interval p03,
			  interval p12, interval p13, interval p23) {
  interval  p0_123 = p01 + p02 + p03;
  interval  p1_023 = p01 + p12 + p13;
  interval  p2_013 = p02 + p12 + p23;
  interval  p3_012 = p03 + p13 + p23;
  interval  p01_23 = p02 + p03 + p12 + p13;
  interval  p02_13 = p01 + p03 + p12 + p23;
  interval  p03_12 = p01 + p02 + p13 + p23;
  interval  F01_23 = p01 * p23 * interMath::sqrt(p01_23);
  interval  F02_13 = p02 * p13 * interMath::sqrt(p02_13);
  interval  F03_12 = p03 * p12 * interMath::sqrt(p03_12);
  interval  F0_123 = (p12*p13+p12*p23+p13*p23)*interMath::sqrt(p0_123);
  interval  F1_023 = (p02*p03+p02*p23+p03*p23)*interMath::sqrt(p1_023);
  interval  F2_013 = (p01*p03+p01*p13+p03*p13)*sqrt01(p2_013);
  interval  F3_012 = (p01*p02+p01*p12+p02*p12)*interMath::sqrt(p3_012);
    return two*(F01_23+F02_13+F03_12+F0_123+F1_023+F2_013+F3_012);
}

interval selling_surface_nn2_013_wide(interval  p01,interval p02,interval p03,
			  interval p12, interval p13, interval p23) {
 return    selling_surface_num2_013_approx_wide(p01,p02,p03,p12,p13,p23) - bcc_value;
}

interval selling_surface_num01_23_approx_wide(interval  p01,interval p02,interval p03,
			  interval p12, interval p13, interval p23) {
 interval  p0_123 = p01 + p02 + p03;
  interval  p1_023 = p01 + p12 + p13;
  interval  p2_013 = p02 + p12 + p23;
  interval  p3_012 = p03 + p13 + p23;
  interval  p01_23 = p02 + p03 + p12 + p13;
  interval  p02_13 = p01 + p03 + p12 + p23;
  interval  p03_12 = p01 + p02 + p13 + p23;
  interval  F01_23 = p01 * p23 * sqrt01(p01_23);
  interval  F02_13 = p02 * p13 * interMath::sqrt(p02_13);
  interval  F03_12 = p03 * p12 * interMath::sqrt(p03_12);
  interval  F0_123 = (p12*p13+p12*p23+p13*p23)*interMath::sqrt(p0_123);
  interval  F1_023 = (p02*p03+p02*p23+p03*p23)*interMath::sqrt(p1_023);
  interval  F2_013 = (p01*p03+p01*p13+p03*p13)*interMath::sqrt(p2_013);
  interval  F3_012 = (p01*p02+p01*p12+p02*p12)*interMath::sqrt(p3_012);
 return   two*(F01_23+F02_13+F03_12+F0_123+F1_023+F2_013+F3_012);
}

interval selling_surface_nn01_23_wide(interval  p01,interval p02,interval p03,
			  interval p12, interval p13, interval p23) {
return   selling_surface_num01_23_approx_wide(p01,p02,p03,p12,p13,p23) - bcc_value;
}


/*
Note: 5/19/2012.
This is code written in 3/2012.  The code for the root function
seems to be missing, and I don't know what happened to it.
I'll comment out this function for now.

interval selling_homog_wide(interval  y1,interval y2,interval y3,
			  interval y4, interval y5, interval y6) {
return 
   (selling_surface_num_wide (y1,y2,y3,y4,y5,y6)) -
  (bcc_value)*(root 6 (selling_volume2_wide (y1,y2,y3,y4,y5,y6) pow 5));
}
*/

