##################################
################ GAP program for the paper Garonzi, Margolis "The Herzog-Schonheim Conjecture for simple and symmetric groups"
#################################

########### the J-function (Introduction)
JFunction := function(G)
local LS, res, U, inds, ind;
LS := ConjugacyClassesSubgroups(G);
res := 0;
inds := [ ];
for U in LS do
  Add(inds, Index(G, Representative(U)));
od;
inds := Set(inds);
for ind in inds do
  res := res + (1/ind);
od;
return res;
end;


#################### Section 2
##
### for a given order calculate all the values of the J-function for groups of this order. Needed in Lemma 2.3
SetJFunctionOrder := function(n)
local L, res;
L := AllGroups(n);
res := List(L, JFunction);
return Set(res);
end;
List([7..15], SetJFunctionOrder);

###### verifying Proposition 2.5 (only M11 here, rest in Mathematica)
JFunction(MathieuGroup(11)) < 2;


################### Section 3
### Proposition 3.2
# small degree
SnValues := List([3..13], x -> JFunction(SymmetricGroup(x)));; # this takes around 12 minutes 
AnValues := List([3..13], x -> JFunction(AlternatingGroup(x)));; # this takes around 3 minutes
# varifying claim (a) for small degree
List(SnValues{[1..4]}, x -> x <= 5/2);
List(SnValues{[1..4]}, x -> x = 5/2);
List(SnValues{[5..11]}, x -> x < 2);
# varifying claim (b) for small degree
List(AnValues{[1..6]}, x -> x <= 11/6);
List(AnValues{[1..6]}, x -> x = 11/6);
List(AnValues{[7..11]}, x -> x < 4/3);
# the paragraph after equation (5), i.e. verifying the claims for 14 <= n <= 19
AnValues[11] < 111/100;
# getting the orders of primitive subgroups of A_n for 14 <= n <= 19 exluding A_{n-1}. These are used afterwards in the Mathematica part
OrdsPrimAn := function(n)
local res, L, H;
res := [ ];
L := AllPrimitiveGroups(DegreeOperation, n);
for H in L do
  if Intersection(H, AlternatingGroup(n)) = H and Order(H) <> Order(AlternatingGroup(n)) then
    Add(res, Order(H));
  fi;
od;
return Set(res);
end;
###
# Claim after Equation (7)
SPlusWnByAn := function(n)
local G;
G := AlternatingGroup(n);
return ( Sum(OrdsPrimAn(n)) + Order(G)*( (3*n/n^3) + (1/Binomial(n,2)) + (1/Binomial(n,3)) ) )/Order(G);
end;
List([20..43], n -> SPlusWnByAn(n) <= n^2/10); # for alternating groups
########################################################
########## Section 4
#######################################
# Auxiliry programs to compute the orders of finite simple classical group of Lie type
PSLnqOrder := function(n,q)
local ord, i;
ord := q^((1/2)*n*(n-1))/Gcd(q-1, n);
for i in [2..n] do
  ord := ord*(q^i-1);
od;
return ord;
end;

PSUnqOrder := function(n,q)
local ord, i;
ord := q^((1/2)*n*(n-1))/Gcd(q+1, n);
for i in [2..n] do
  ord := ord*(q^i - (-1)^i);
od;
return ord;
end;

## from the nxn-matrices, so input n must be even 
PSpnqOrder := function(n,q)
local ord, i;
n := n/2;
ord := q^(n^2)/Gcd(q-1, 2);
for i in [1..n] do
  ord := ord*(q^(2*i)-1);
od;
return ord;
end;


## from the nxn-matrices, so input n must be odd 
POmeganqOrder := function(n,q)
local ord, i;
n := (n-1)/2;
ord := q^(n^2)/Gcd(q-1, 2);
for i in [1..n] do
  ord := ord*(q^(2*i)-1);
od;
return ord;
end;

## from the nxn-matrices, so input n must be even 
POmegaPlusnqOrder := function(n,q)
local ord, i;
n := n/2;
ord := q^(n^2-n)*((q^n)-1)/Gcd((q^n)-1, 4);
for i in [1..n-1] do
  ord := ord*(q^(2*i)-1);
od;
return ord;
end;

## from the nxn-matrices, so input n must be even 
POmegaMinusnqOrder := function(n,q)
local ord, i;
n := n/2;
ord := q^(n^2-n)*((q^n)+1)/Gcd((q^n)+1, 4);
for i in [1..n-1] do
  ord := ord*(q^(2*i)-1);
od;
return ord;
end;
#####################
## auxilary program which records the number of divisors of the order of finite simple classical groups for given parameters
NrDivisorsOfOrderClassicalGroups := function(n, q)
local res, ord, divs, l, d;
res := [ ];
ord := PSLnqOrder(n,q);
Add(res, Tau(ord));
ord := PSUnqOrder(n,q);
Add(res, Tau(ord));
if n mod 2 = 0 then
  ord := PSpnqOrder(n,q);
  Add(res, Tau(ord));
fi;
if n mod 2 = 1 then 
  ord := POmeganqOrder(n,q);
  Add(res, Tau(ord));
fi;
if n mod 2 = 0 then
  ord := POmegaPlusnqOrder(n,q);
  Add(res, Tau(ord));
fi;
if n mod 2 = 0 then
  ord := POmegaMinusnqOrder(n,q);
  Add(res, Tau(ord));
fi;
return res;
end;
###
# obtain data needed for the proof of Proposition 4.6, case q = 2
NrDivisorsOfOrderClassicalGroups(13, 2);
NrDivisorsOfOrderClassicalGroups(14, 2);
# obtain data needed for the proof of Proposition 4.6, case q > 2, n = 13
NrDivisorsOfOrderClassicalGroups(13, 3);
## 
## Checking the cases of small rank and small fields appearing in the proof of Proposition 4.6 for n <= 12
# cases for PSL
LPSL := [ [3,2], [3,3], [3,4], [3,5], [3,7], [3,8], [3,9], [4,2], [4,3], [5,2], [2,8], [2,11], [2,13] ];; # cases [2,4] and [2,5] are A5, case [2,7] is case [3,2], case [2,9] is A6, so they are excluded
List(LPSL, x ->  JFunction(PSL(x[1], x[2])) < 2);
# cases for PSU
LPSU := [ [3,3], [3,4], [3,5], [4,2] ];;
List(LPSU, x ->  JFunction(PSU(x[1], x[2])) < 2);
# cases for PSp
LPSp := [ [4,3], [4,4], [6,2] ];;
List(LPSp, x ->  JFunction(PSp(x[1], x[2])) < 2);
# cases for PSOmegaEpsilon
JFunction(POmega(1,8,2)) < 2;
JFunction(POmega(-1,8,2)) < 2;
