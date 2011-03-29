# parameters
param pi := 3.1415926535897932;
param sqrt2 := 1.414213562373095;
param sqrt3 := 1.732050807568877;

# variables
var x >= 0, <= sqrt2;
var y >= sqrt3, <= 10;
var z >= 1, <= 3;

## objective
maximize objective:  3*x - y;

## equality constraints
pi_sum: x + y + z = pi;

## inequality constraints
c1: x + sqrt2 * y <= sqrt3 + z;

solve;
