## interval arithmetic bounds dart_std4 ##

tau_azim4A 'ID[7043724150]' {(i,j) in dart_std4}:
  tau[j] + 4.72*azim[i,j] - 6.248 >= 0;

tau_azim4B 'ID[6944699408]' {(i,j) in dart_std4}:
  tau[j] + 0.972*azim[i,j] - 1.707 >= 0;

tau_azim4C 'ID[4240815464]' {(i,j) in dart_std4}:
  tau[j] + 0.7573*azim[i,j] - 1.433 >= 0;

tau_azim4D 'ID[3862621143]' {(i,j) in dart_std4}:
  tau[j] - 0.453*azim[i,j] + 0.777 >= 0;  # typo corrected Sep 8 2009 (Thanks to Erin Susick!)


## Tame Table B inequality bounds 

azmin 'ID[5735387903]' {(i,j) in dart_std3} : azim[i,j] >= 0.852;

azmax 'ID[5490182221]' {(i,j) in dart_std3}: azim[i,j] <= 1.893;

tau_azim3A 'ID[3296257235]' {(i,j) in dart_std3}: 
  tau[j]+0.626*azim[i,j] - 0.77 >= 0;

tau_azim3B 'ID[8519146937]' {(i,j) in dart_std3}: 
  tau[j]-0.259*azim[i,j] + 0.32 >= 0;

tau_azim3C 'ID[4667071578]' {(i,j) in dart_std3}: 
  tau[j]-0.507*azim[i,j] + 0.724 >= 0;

# more dart_std3.

tau_azim3D 'ID[1395142356]' {(i,j) in dart_std3}: 
  tau[j] + 0.001 -0.18*(y1[i,j]+y2[i,j]+y3[i,j]-6) - 0.125*(y4[i,j]+y5[i,j]+y6[i,j]-6) >= 0;

solyA 'ID[7394240696]' {(i,j) in dart_std3}: 
  sol[j] - 0.55125 - 0.196*(y4[i,j]+y5[i,j]+y6[i,j]-6) + 0.38*(y1[i,j]+y2[i,j]+y3[i,j]-6) >= 0;

solyB 'ID[7726998381]' {(i,j) in dart_std3}: 
  -sol[j] + 0.5513 + 0.3232*(y4[i,j]+y5[i,j]+y6[i,j]-6) - 0.151*(y1[i,j]+y2[i,j]+y3[i,j]-6) >= 0;

azminA 'ID[4047599236]'  {(i,j) in dart_std3}: azim[i,j] - 1.2308 
  + 0.3639*(y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8) - 0.235*(y1[i,j]-2) - 0.685*(y4[i,j]-2) >= 0;

azmaxA 'ID[3526497018]' {(i,j) in dart_std3}: -azim[i,j] + 1.231 
  - 0.152*(y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8) + 0.5*(y1[i,j]-2) + 0.773*(y4[i,j]-2) >= 0;

rhazminA 'ID[5957966880]' {(i,j) in dart_std3}: rhazim[i,j] - 1.2308 
  + 0.3639*(y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8) - 0.6*(y1[i,j]-2) - 0.685*(y4[i,j]-2) >= 0;

## more interval arithmetic on nonstandard triangles  ##

azminX 'ID[3020140039]' {(i,j) in dartX}: 
  azim[i,j] - 1.629  + 0.402*(y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8) - 0.315*(y1[i,j]-2)  >= 0;

azminY 'ID[9414951439]' {(i,j) in dartY}:
  azim[i,j] - 1.91 + 0.458 * (y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8) - 0.342*(y1[i,j]-2) >= 0;

azminZ 'ID[9995621667]' {(i,j) in dart4_diag3}:
  azim[i,j] - 2.09 + 0.578 * (y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8) - 0.54*(y1[i,j]-2) >= 0;

#branch apex_flat inequality

flattau 'ID[8248508703]' {(i,j) in apex_flat}:
  tau[j] - 0.1 - 0.265*(y5[i,j]+y6[i,j]-4) - 0.06*(y4[i,j]-2.52) 
   - 0.16*(y1[i,j]-2) -  0.115*(y2[i,j]+y3[i,j]-4) >=0;

flatazim 'ID[3318775219]' {(i,j) in apex_flat}:
  azim[i,j] - 1.629 + 0.414*(y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8)
-0.763*(y4[i,j]-2.52) - 0.315*(y1[i,j]-2) >= 0;

flatazimmax 'ID[9922699028]' {(i,j) in apex_flat}:
  -azim[i,j] + 1.6294 - 0.2213*(y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8)
  +0.913*(y4[i,j]-2.52) + 0.728*(y1[i,j]-2) >= 0;

## ZZ SECOND BATCH

#ZZ start



flatazim2 'ID[5000076558]' {(i1,i,i3,j) in e_dart : (i,j) in apex_flat}:
  azim[i3,j] - 1.083 + 0.6365*(y1[i,j]-2) - 0.198*(y2[i,j]-2)
  +0.352*(y3[i,j]-2) + 0.416*(y4[i,j]-2.52)
  -0.66*(y5[i,j]-2) + 0.071*(y6[i,j]-2) >= 0;

flatazim3 'ID[5000076558]' {(i1,i,i3,j) in e_dart : (i,j) in apex_flat}:
  azim[i1,j] - 1.083 + 0.6365*(y1[i,j]-2) - 0.198*(y3[i,j]-2)
  +0.352*(y2[i,j]-2) + 0.416*(y4[i,j]-2.52)
  -0.66*(y6[i,j]-2) + 0.071*(y5[i,j]-2) >= 0;

flatrhazim 'ID[9251360200]' {(i,j) in apex_flat}:
  rhazim[i,j]
  -1.629 - 0.866*(y1[i,j]-2) + 0.3805*(y2[i,j]+y3[i,j]-4)
  -0.841*(y4[i,j]-2.52) + 0.501*(y5[i,j]+y6[i,j]-4) >= 0;

flatrhazim2 'ID[9756015945]' {(i1,i,i3,j) in e_dart: (i,j) in apex_flat}:
  rhazim[i3,j] -1.08
  +0.6362*(y1[i,j]-2) -0.565*(y2[i,j]-2)+0.359*(y3[i,j]-2)
  +0.416*(y4[i,j]-2.52) -0.666*(y5[i,j]-2) +0.061*(y6[i,j]-2) >=0;

flatrhazim3 'ID[9756015945]' {(i1,i,i3,j) in e_dart: (i,j) in apex_flat}:
  rhazim[i3,j] -1.08
  +0.6362*(y1[i,j]-2) -0.565*(y3[i,j]-2)+0.359*(y2[i,j]-2)
  +0.416*(y4[i,j]-2.52) -0.666*(y6[i,j]-2) +0.061*(y5[i,j]-2) >=0;

#branch apex_sup_flat inequality


tausf2 'ID[4840774900]'  {(i,j) in apex_sup_flat}:
 tau[j]     -0.1054 
    -0.14132*(y1[i,j]+ y2[i,j]/2 + y3[i,j]/2 - 4)
    -0.36499*(y5[i,j]+y6[i,j]-4) >= 0;

tausf4 'ID[1642527039]'  {(i,j) in apex_sup_flat}:
 tau[j]     -0.128 
- 0.053*((y5[i,j]+y6[i,j]-4) - (2.75/2)*(y4[i,j]- sqrt8)) >= 0;

tausf5 'ID[7863247282]' {(i,j) in apex_sup_flat}:
 tau[j] - 0.053*((y5[i,j]+y6[i,j]-4) - (2.75/2)*(y4[i,j]- sqrt8))
    -0.12 
    -0.14132*(y1[i,j]+ y2[i,j]/2 + y3[i,j]/2 - 4)
    -0.328*(y4[i,j]+y5[i,j]-4) >= 0;

azimf3 'ID[7718591733]' {(i,j) in apex_sup_flat}:
  azim[i,j] - 0.955 
   - 0.2356*(y1[i,j]-2)
       +0.32*(y2[i,j]-2) + 0.792*(y3[i,j]-2)
   -0.707*(y4[i,j]-2) 
        + 0.0844*(y5[i,j]-2) + 0.821*(y6[i,j]-sqrt8) >=0;

azimsf2 'ID[3566713650]' {(i,j) in apex_sup_flat}:
  -azim[i,j] + 1.911 +1.01 *(y1[i,j] - 2)
  -0.284*(y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8)
   +1.07*(y4[i,j]-sqrt8) >= 0;

azimsf1 'ID[1085358243]' {(i,j) in apex_sup_flat}:
  azim[i,j] - 1.903 - 0.4*(y1[i,j] - 2)
  +0.49688*(y2[i,j]+y3[i,j]+y5[i,j]+y6[i,j]-8)
   -(y4[i,j]-sqrt8) >= 0;






#branch apex_A inequality.

apieceazim 'ID[5760733457]' {(i,j) in apex_A}:
  azim[i,j] - 1.0705 
  -0.1*(y1[i,j]-2) + 0.424*(y2[i,j]-2) + 0.424*(y3[i,j]-2) 
  -0.594*(y4[i,j]-2) + 0.124*(y5[i,j]-2.52) + 0.124*(y6[i,j]-2.52) >= 0;

apiecerhazim 'ID[2563100177]' {(i,j) in apex_A}:
  rhazim[i,j] - 1.0685 
  -0.4635*(y1[i,j]-2) + 0.424*(y2[i,j]-2) + 0.424*(y3[i,j]-2) 
  -0.594*(y4[i,j]-2) + 0.124*(y5[i,j]-2.52) + 0.124*(y6[i,j]-2.52) >= 0;

apiecetau 'ID[7931207804]' {(i,j) in apex_A}:
  tau[j] - 0.27
  +0.0295*(y1[i,j]-2) - 0.0778*(y2[i,j]-2) - 0.0778*(y3[i,j]-2) 
  -0.37*(y4[i,j]-2) - 0.27*(y5[i,j]-2.52) - 0.27*(y6[i,j]-2.52) >= 0;

#branch std3_small inequality

std3_smalltau 'ID[9225295803]' {(i,j) in dart_std3_small}:
  tau[j] +0.0034
  -0.166*(y1[i,j]+y2[i,j]+y3[i,j]-6) -0.22*(y4[i,j]+y5[i,j]+y6[i,j]-6) >=0;

std3_smalldih 'ID[9291937879]' {(i,j) in dart_std3_small}:
  azim[i,j] - 1.23
  -0.235*(y1[i,j]-2) + 0.362*(y2[i,j]+y3[i,j]-4)
  -0.694*(y4[i,j]-2) + 0.26*(y5[i,j]+y6[i,j]-4) >=0;

#branch std3_big inequality

std3_bigtau 'ID[7761782916]' {(i,j) in dart_std3_big}:
  tau[j] - 0.05 -0.137*(y1[i,j]+y2[i,j]+y3[i,j]-6)
  -0.17*(y4[i,j]+y5[i,j]+y6[i,j]-6.25) >= 0;

std3_bigsol 'ID[6224332984]'  {(i,j) in dart_std3_big}:
  sol[j] - 0.589 +0.39*(y1[i,j]+y2[i,j]+y3[i,j]-6)
  -0.235*(y4[i,j]+y5[i,j]+y6[i,j]-6.25) >= 0;



#branch LOWSMALLnode inequality

azimlowsmall 'ID[9229542852]' {(i,j) in dart_std3_small_200_218}:
  azim[i,j] - 1.230
  -0.2357*(y1[i,j]-2)
  +0.2493*(y2[i,j]+y3[i,j]-4)
  -0.682*(y4[i,j]-2)
  +0.3035*(y5[i,j]+y6[i,j]-4) >= 0;

azimlowsmallmax 'ID[1550635295]' {(i,j) in dart_std3_small_200_218}:
  -azim[i,j] + 1.232
  +0.261*(y1[i,j]-2)
  -0.203*(y2[i,j]+y3[i,j]-4)
  +0.772*(y4[i,j]-2)
  -0.191*(y5[i,j]+y6[i,j]-4) >= 0;

taulowsmall 'ID[4491491732]' {(i,j) in dart_std3_small_200_218}:
  tau[j]  + 0.0008
  -0.1631*(y1[i,j]+y2[i,j]+y3[i,j]-6)
  -0.2127*(y4[i,j]+y5[i,j]+y6[i,j]-6) >= 0;

taulowbig 'ID[8611785756]'  {(i,j) in dart_std3_big_200_218}:
  sol[j] - 0.589 +0.24*(y1[i,j]+y2[i,j]+y3[i,j]-6)
  -0.16*(y4[i,j]+y5[i,j]+y6[i,j]-6.25) >= 0;


# branch node_200_218 LLL.

#branch HIGH node inequality

hiazimA 'ID[2151506422]' {(i,j) in apex_std3_hll} :
   azim[i,j] >= 1.2777 
     + 0.281*(y1[i,j]-2.18)
     - 0.278364*(y2[i,j]-2)
     -0.278364*(y3[i,j]-2)
     + 0.7117*(y4[i,j]-2)
      -0.34336*(y5[i,j]-2) 
      -0.34336*(y6[i,j]-2);

hiazimB 'ID[6836427086]' {(i,j) in apex_std3_hll} :
   -azim[i,j] >= -1.27799
     -0.356217*(y1[i,j]-2.18)
     +0.229466*(y2[i,j]-2)
     +0.229466*(y3[i,j]-2)
     -0.949067*(y4[i,j]-2)
     +0.172726*(y5[i,j]-2) 
     +0.172726*(y6[i,j]-2);
     #{-0.356217, 0.229466, 0.229466, -0.949067, 0.172726, 0.172726}

hiazimC 'ID[3636849632]' {(i,j) in apex_std3_hll} :
   tau[j] >=  0.0345
     +0.185545*(y1[i,j]-2.18)
     +0.193139*(y2[i,j]-2)
     +0.193139*(y3[i,j]-2)
     +0.170148*(y4[i,j]-2)
     +0.13195*(y5[i,j]-2) 
     +0.13195*(y6[i,j]-2);
     #{0.185545, 0.193139, 0.193139, 0.170148, 0.13195, 0.13195}

hiazimD 'ID[5298513205]' {(i,j) in apex_std3_hll} :
   azim2[i,j] >= 1.185
     -0.302913*(y1[i,j]-2.18)
     +0.214849*(y2[i,j]-2)
     -0.163775*(y3[i,j]-2)
     -0.443449*(y4[i,j]-2)
     +0.67364*(y5[i,j]-2) 
     -0.314532*(y6[i,j]-2);
     # {-0.302913, 0.214849, -0.163775, -0.443449, 0.67364, -0.314532}

hiazimE 'ID[5298513205]' {(i,j) in apex_std3_hll} : # 2<->3, 5<->6 sym.
   azim3[i,j] >= 1.185
     -0.302913*(y1[i,j]-2.18)
     +0.214849*(y3[i,j]-2)
     -0.163775*(y2[i,j]-2)
     -0.443449*(y4[i,j]-2)
     +0.67364*(y6[i,j]-2) 
     -0.314532*(y5[i,j]-2);
     # {-0.302913, 0.214849, -0.163775, -0.443449, 0.67364, -0.314532}

hiazimF 'ID[7743522046]' {(i,j) in apex_std3_hll} :
   -azim2[i,j] >= -1.1865
     +0.20758*(y1[i,j]-2.18)
     -0.236153*(y2[i,j]-2)
     +0.14172*(y3[i,j]-2)
     +0.263834*(y4[i,j]-2)
     -0.771203*(y5[i,j]-2) 
     +0.0457292*(y6[i,j]-2);
     #{0.20758, -0.236153, 0.14172, 0.263834, -0.771203, 0.0457292};

hiazimG 'ID[7743522046]' {(i,j) in apex_std3_hll} : # 2<->3, 5<->6 sym.
   -azim3[i,j] >= -1.1865
     +0.20758*(y1[i,j]-2.18)
     -0.236153*(y3[i,j]-2)
     +0.14172*(y2[i,j]-2)
     +0.263834*(y4[i,j]-2)
     -0.771203*(y6[i,j]-2) 
     +0.0457292*(y5[i,j]-2);
     #{0.20758, -0.236153, 0.14172, 0.263834, -0.771203, 0.0457292};


# branch HLL SMALL 

hllsmallazimA 'ID[8657368829]' {(i,j) in apex_std3_hll inter dart_std3_small} :
   azim[i,j] >= 1.277
     +0.273298*(y1[i,j]-2.18)
     -0.273853*(y2[i,j]-2)
     -0.273853*(y3[i,j]-2)
     +0.708818*(y4[i,j]-2)
     -0.313988*(y5[i,j]-2) 
     -0.313988*(y6[i,j]-2);
     #{0.273298, -0.273853, -0.273853, 0.708818, -0.313988, -0.313988}


hllsmallazimB 'ID[6619134733]' {(i,j) in apex_std3_hll inter dart_std3_small} :
   -azim[i,j] >= -1.27799
     -0.439002*(y1[i,j]-2.18)
     +0.229466*(y2[i,j]-2)
     +0.229466*(y3[i,j]-2)
     -0.771733*(y4[i,j]-2)
      +0.208429*(y5[i,j]-2) 
     +0.208429*(y6[i,j]-2);
     # {-0.439002, 0.229466, 0.229466, -0.771733, 0.208429, 0.208429}

hllsmallazimC 'ID[1284543870]' {(i,j) in apex_std3_hll inter dart_std3_small} :
   azim2[i,j] >= 1.185
     -0.372262*(y1[i,j]-2.18)
     +0.214849*(y2[i,j]-2)
     -0.163775*(y3[i,j]-2)
     -0.293508*(y4[i,j]-2)
     +0.656172*(y5[i,j]-2) 
     -0.267157*(y6[i,j]-2);
   # {-0.372262, 0.214849, -0.163775, -0.293508, 0.656172, -0.267157};

hllsmallazimD 'ID[1284543870]' {(i,j) in apex_std3_hll  inter dart_std3_small} :
   azim3[i,j] >= 1.185  
     -0.372262*(y1[i,j]-2.18)
     +0.214849*(y3[i,j]-2)
     -0.163775*(y2[i,j]-2)
     -0.293508*(y4[i,j]-2)
     +0.656172*(y6[i,j]-2) 
     -0.267157*(y5[i,j]-2);
   # {-0.372262, 0.214849, -0.163775, -0.293508, 0.656172, -0.267157};

hllsmallazimE 'ID[4041673283]' {(i,j) in apex_std3_hll inter dart_std3_small} :
   -azim2[i,j] >= -1.1864
     +0.20758*(y1[i,j]-2.18)
     -0.236153*(y2[i,j]-2)
     +0.14172*(y3[i,j]-2)
     +0.263109*(y4[i,j]-2)
     -0.737003*(y5[i,j]-2) 
     +0.12047*(y6[i,j]-2);
  #{0.20758, -0.236153, 0.14172, 0.263109, -0.737003, 0.12047};

hllsmallazimF 'ID[4041673283]' {(i,j) in apex_std3_hll  inter dart_std3_small} :
   -azim3[i,j] >= -1.1864  # symmetry 2<->3, 5<->6.
     +0.20758*(y1[i,j]-2.18)
     -0.236153*(y3[i,j]-2)
     +0.14172*(y2[i,j]-2)
     +0.263109*(y4[i,j]-2)
     -0.737003*(y6[i,j]-2) 
     +0.12047*(y5[i,j]-2);
  #{0.20758, -0.236153, 0.14172, 0.263109, -0.737003, 0.12047};

# branch apex_flat:

tauhighlow 'ID[8282573160]'  {(i,j) in dart_8282573160} :
  tau[j] - 0.1413
  -0.214*(y1[i,j]-2.18)
  -0.1259*(y2[i,j]+y3[i,j]-4)
  -0.067*(y4[i,j]-2.52)
  -0.241*(y5[i,j]+y6[i,j]-4) >=0;

# branch BIG/SMALL/edge EXTRAHIGH/MEDIUMHIGH

#a
azim_med_big 'ID[3872614111]' {(i,j) in  dart_3872614111} :
  -azim[i,j] >= -1.542
     -0.362519*(y1[i,j]-2.36)
      +0.298691*(y2[i,j]-2)
      +0.287065*(y3[i,j]-2)
      -0.920785*(y4[i,j]-2.25)
      +0.190917*(y5[i,j]-2)
      +0.219132*(y6[i,j]-2) ;
   #  {-0.362519, 0.298691, 0.287065, -0.920785, 0.190917, 0.219132};

#b
azim_med_small 'ID[3139693500]'  {(i,j) in  dart_3139693500}  :
  -azim[i,j] >= -1.542
     -0.346773*(y1[i,j]-2.36)
      +0.300751*(y2[i,j]-2)
      +0.300751*(y3[i,j]-2)
      -0.702567*(y4[i,j]-2.25)
      +0.172726*(y5[i,j]-2)
      +0.172727*(y6[i,j]-2) ;
   # {-0.346773, 0.300751, 0.300751, -0.702567, 0.172726, 0.172727};

#c
azim2_extra_small 'ID[4841020453]'  {(i,j) in  dart_4841020453} :
  -azim[i,j] >= -1.542
     -0.490439*(y1[i,j]-2.36)
      +0.318125*(y2[i,j]-2)
      +0.32468*(y3[i,j]-2)
      -0.740079*(y4[i,j]-2.25)
      +0.178868*(y5[i,j]-2)
      +0.205819*(y6[i,j]-2) ;
   #  {-0.490439, 0.318125, 0.32468, -0.740079, 0.178868, 0.205819};

#d
azim_extra_big 'ID[9925287433]'   {(i,j) in  dart_9925287433} :
   -azim[i,j] >= -1.542
     -0.490439*(y1[i,j]-2.36)
      +0.321849*(y2[i,j]-2)
      +0.320956*(y3[i,j]-2)
      -1.00902*(y4[i,j]-2.25)
      +0.240709*(y5[i,j]-2)
      +0.218081*(y6[i,j]-2) ;
   # {-0.490439, 0.321849, 0.320956, -1.00902, 0.240709, 0.218081};


#e
azim2_med_big 'ID[7409690040]'   {(i,j) in  dart_7409690040 } :
  azim2[i,j] >= 1.0494
     -0.297823*(y1[i,j]-2.36)
      +0.215328*(y2[i,j]-2)
      -0.0792439*(y3[i,j]-2)
      -0.422674*(y4[i,j]-2.25)
      +0.647416*(y5[i,j]-2)
      -0.207561*(y6[i,j]-2) ;
   #  {-0.297823, 0.215328, -0.0792439, -0.422674, 0.647416, -0.207561};


#e sym
azim3_med_big 'ID[7409690040]'   {(i,j) in  dart_7409690040 } :
  azim3[i,j] >= 1.0494
     -0.297823*(y1[i,j]-2.36)
      +0.215328*(y3[i,j]-2)
      -0.0792439*(y2[i,j]-2)
      -0.422674*(y4[i,j]-2.25)
      +0.647416*(y6[i,j]-2)
      -0.207561*(y5[i,j]-2) ;
   #  {-0.297823, 0.215328, -0.0792439, -0.422674, 0.647416, -0.207561};


#f
azim2_med_small 'ID[4002562507]'   {(i,j) in  dart_4002562507 } :
  azim2[i,j] >= 1.0494
     -0.29013*(y1[i,j]-2.36)
      +0.215328*(y2[i,j]-2)
      -0.0715511*(y3[i,j]-2)
      -0.267157*(y4[i,j]-2.25)
      +0.650269*(y5[i,j]-2)
      -0.295198*(y6[i,j]-2) ;
   #  {-0.29013, 0.215328, -0.0715511, -0.267157, 0.650269, -0.295198};


#f sym
azim3_med_small 'ID[4002562507]'   {(i,j) in  dart_4002562507 } :
  azim3[i,j] >= 1.0494
     -0.29013*(y1[i,j]-2.36)
      +0.215328*(y3[i,j]-2)
      -0.0715511*(y2[i,j]-2)
      -0.267157*(y4[i,j]-2.25)
      +0.650269*(y6[i,j]-2)
      -0.295198*(y5[i,j]-2) ;
   #  {-0.29013, 0.215328, -0.0715511, -0.267157, 0.650269, -0.295198};


#g
azim_extra_small 'ID[5835568093]'   {(i,j) in  dart_5835568093 } :
  azim2[i,j] >= 1.0494
     -0.404131*(y1[i,j]-2.36)
      +0.212119*(y2[i,j]-2)
      -0.0402827*(y3[i,j]-2)
      -0.299046*(y4[i,j]-2.25)
      +0.643273*(y5[i,j]-2)
      -0.266118*(y6[i,j]-2) ;
   # {-0.404131, 0.212119, -0.0402827, -0.299046, 0.643273, -0.266118};


#g sym
azim3_extra_small 'ID[5835568093]'   {(i,j) in  dart_5835568093 } :
  azim3[i,j] >= 1.0494
     -0.404131*(y1[i,j]-2.36)
      +0.212119*(y3[i,j]-2)
      -0.0402827*(y2[i,j]-2)
      -0.299046*(y4[i,j]-2.25)
      +0.643273*(y6[i,j]-2)
      -0.266118*(y5[i,j]-2) ;
   # {-0.404131, 0.212119, -0.0402827, -0.299046, 0.643273, -0.266118};


#h
azim2_extra_big 'ID[1894886027]'   {(i,j) in  dart_1894886027 } :
  azim2[i,j] >= 1.0494
     -0.401543*(y1[i,j]-2.36)
      +0.207551*(y2[i,j]-2)
      -0.0294227*(y3[i,j]-2)
      -0.494954*(y4[i,j]-2.25)
      +0.605453*(y5[i,j]-2)
      -0.156385*(y6[i,j]-2) ;
   # {-0.401543, 0.207551, -0.0294227, -0.494954, 0.605453, -0.156385};

#h sym
azim3_extra_big 'ID[1894886027]'   {(i,j) in  dart_1894886027 } :
  azim3[i,j] >= 1.0494
     -0.401543*(y1[i,j]-2.36)
      +0.207551*(y3[i,j]-2)
      -0.0294227*(y2[i,j]-2)
      -0.494954*(y4[i,j]-2.25)
      +0.605453*(y6[i,j]-2)
      -0.156385*(y5[i,j]-2) ;
   # {-0.401543, 0.207551, -0.0294227, -0.494954, 0.605453, -0.156385};


# ZZ end




# darts with y4>= 2.52, y6 [2.52,s8], others [2,2.52]
big5azim46 'ID[1812128999]' {(i1,i,i3,j) in e_dart: (i1,j) in apex5}: 
  azim[i,j]  - 1.448
  -0.266*(y1[i,j]-2) + 0.295*(y2[i,j]-2) + 0.57*(y3[i,j]-2)
   -0.745*(2.52-2.52)   + 0.268*(y5[i,j]-2) + 0.385*(y6[i,j]-2.52) >= 0;

big4azim46 'ID[1812128999]' {(i1,i,i3,j) in e_dart: (i1,j) in apex4}: 
  azim[i,j]  - 1.448
  -0.266*(y1[i,j]-2) + 0.295*(y2[i,j]-2) + 0.57*(y3[i,j]-2)
  -0.745*(sqrt8-2.52)  +0.268*(y5[i,j]-2) + 0.385*(y6[i,j]-2.52) >= 0;


#branch azim apex_A-BIGPIECE inequality
#We get six inequalities from a single non-linear inequality,
#  depending on the constraints on y4, and symmetries.


# permute the y coordinates so that [i,j] is apex_A
# y6 is opposite, y5 is other long in apex_A.
apieceazim3 'ID[1812128999]' {(i1,i,i3,j) in e_dart: (i,j) in apex_A}: 
  azim[i1,j]  - 1.448
  -0.266*(y3[i,j]-2) + 0.295*(y1[i,j]-2) + 0.57*(y2[i,j]-2)
  -0.745*(y6[i,j]-2.52)  +0.268*(y4[i,j]-2) + 0.385*(y5[i,j]-2.52) >= 0;

# Three more obtained from preceding by y2<->y3, y5<->y6.
# darts with y4>= 2.52, y5 [2.52,s8], others [2,2.52]
big5azim56 'ID[1812128999]' {(i1,i2,i,j) in e_dart: (i1,j) in apex5}: 
  azim[i,j]  - 1.448
  -0.266*(y1[i,j]-2) + 0.295*(y3[i,j]-2) + 0.57*(y2[i,j]-2)
  -0.745*(2.52-2.52)  +0.268*(y6[i,j]-2) + 0.385*(y5[i,j]-2.52) >= 0;

big4azim56 'ID[1812128999]' {(i1,i2,i,j) in e_dart: (i1,j) in apex4}: 
  azim[i,j]  - 1.448
  -0.266*(y1[i,j]-2) + 0.295*(y3[i,j]-2) + 0.57*(y2[i,j]-2)
  -0.745*(sqrt8-2.52)  +0.268*(y6[i,j]-2) + 0.385*(y5[i,j]-2.52) >= 0;

# permute the y coordinates so that [i,j] is apex_A
# y5 is opposite, y6 is other long.
apieceazim2 'ID[1812128999]' {(i1,i,i3,j) in e_dart: (i,j) in apex_A}: 
  azim[i3,j]  - 1.448
  -0.266*(y2[i,j]-2) + 0.295*(y1[i,j]-2) + 0.57*(y3[i,j]-2)
  -0.745*(y5[i,j]-2.52)  +0.268*(y4[i,j]-2) + 0.385*(y6[i,j]-2.52) >= 0;

## MAIN ESTIMATE on big faces ##

tau4s 'ID[9563139965]' {j in std4_diag3}: tau[j] >= 0.496;
d21 'ID[6988401556]' {(i,j) in apex_flat}: tau[j] >= 0.103;  # cf. tame table d[2,1], 
tauAh 'ID[8082208587]' {(i,j) in apex_A}: tau[j] >= 0.2759; # cf. tame table d[1,2].

#this kills all std4_diag3.  It holds more strongly with the constant 0.49.
tauZ 'ID[7676202716] 49c' {(i1,i2,i3,j) in e_dart : j in std4_diag3}:
     tau[j] - 0.45 *(y5[i1,j] + y6[i1,j] + y5[i3,j] + y6[i3,j]-8.472) >= 0.46; 

