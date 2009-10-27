
let z6=ds"0 0 0 0 0 0";;
let z3=ds"0 0 0";;
let z=d"0";;
let twos=ds"2 2 2 2 2 2";;
let r6=ds"2.52 2.52 2.52 2.52 2.52 2.52";;
let amin=ds"2 2 2 2 2.52 2.52";
let amax=ds"2 2 2 2.52 s8 s8";
let azim1=d"1 0 0";
let azim2=d"0 1 0";
let azim3=d"0 0 1";
let rhzim1=azim1;
let rhzim2=azim2;
let rhzim3=azim3;

let a = blank;

let ineqlist:ineq list = [
  {
  id="3336871894";
    constrain=NONE;
    sgn=GE;
    xmin=twos
    xmax=r6;
    c0=z;
    c=z6;
    p=z6;
    azim=z3;
    rhzim=z3;
    sol0=z;
    tau0=d"1";
  };

  {
    id="8880534953";
    constrain=NONE;
    sgn=GT;
    xmin=amin;
    xmax=amax;
    c0=d"0.2759";
    c=z6;
    p=z6;
    azim=z3;
    rhzim=z3;
    sol0=z;
    tau0=d"1";
  };

  {
    id="5735387903";
    constrain=NONE;
    sgn=GT;
    xmin=twos;
    xmax=r6;
    c0=d"1.";
    c=z6;
    p=z6;
    azim=z3;
    rhzim=z3;
    sol0=z;
    tau0=z;
  };
];;

1;;
