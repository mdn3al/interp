/*
bok.zip
bok.pdf
pag 147   159 189

I ::= x | y | z | ...
N ::= 0 | 1 | 2 | ...
B ::= true | false | E >E | ...
E ::= I | N | E + E | E - E | E * E | ...
C ::= skip | assign(I;E) | if (B;C;C) | while(B;C) | seq(C;C)

For instance, the factorial program:

y := 1; while x > 0 do y := y * x; x := x - 1 od

is represented by the abstract syntax:

seq(assign(y; 1); while(x > 0; seq(assign(y; y * x); assign(x; x - 1))))

Moreover, a binding environment is a mapping from identiers to values (in
our case integers) which could be represented as a list of pairs of variables and
integers.
Now write an interpreter eval=3 which relates an initial binding environment
and a command C to the new binding environment obtained by \executing"
C. For instance, if x maps to 5 in sigma and c is the program above the goal
eval (sigma; c;X) should result in a new binding environment where x maps to
0 and y maps to 120 (i.e. the factorial of 5).
*/

%domains
%  I=symbol
%  N=integer
%  B=boolean;mM(E,E);e(E,E)
%  E=I;N;plus(E,E);minus(E,E);ori(E,E);imp(E,E)
%  C=skip;assign(I,E);if(B,C,C);while(B,C);seq(C,C)
  
%predicates
%  eval(C)
%clauses

eval(Sigma,Cmd,X):-
  initializari(Sigma),
  eval(Cmd).
%  afisazaVal(Sigma).

afisazaVal([]):-!.
afisazaVal([intreg(X)|Sigma]):-
  intreg(X,V),
  write(X),write(' = '),write(V),write(' '),
  afisazaVal(Sigma).
%intreg(_,_).

initializari([]).
initializari([initr(X,V)|Sigma]):-
  assertz(intreg(X,V)),
  initializari(Sigma).

eval(skip).
eval(if(C,I1,I2)):-
  C,eval(I1).
eval(if(C,I1,I2)):-
  eval(I2).
eval(while(B,_)):-
  not(B).
eval(while(B,C)):-
  B,
  eval(C),
  eval(while(B,C)).
eval(seq(I1,I2)):-
  eval(I1),
  eval(I2).
eval(inc(X)):-
  intreg(X,V),
  retract(intreg(X,V)),
  Vn is V+1,
  assertz(intreg(X,Vn)).
eval(dec(X)):-
  intreg(X,V),
  retract(intreg(X,V)),
  Vn is V-1,
  assertz(intreg(X,Vn)).
eval(assign(X,Constanta)):-
  retract(intreg(X,V1)),
  assertz(intreg(X,Constanta)).
eval(assign(X,V)):-
  intreg(V,V0),
  retract(intreg(X,V1)),
  assertz(intreg(X,V0)).
eval(assign(X,suma(Y,Z))):-
  intreg(Y,Vy),
  intreg(Z,Vz),
  retract(intreg(X,V1)),
  V is Vy+Vz,
  assertz(intreg(X,V)).
eval(assign(X,produs(Y,Z))):-
  intreg(Y,Vy),
  intreg(Z,Vz),
  retract(intreg(X,V1)),
  V is Vy*Vz,
  assertz(intreg(X,V)).

nenegativ(X):-
  intreg(X,V),
  V>0.
%goal:-
%?- eval(
%  [initr(x,10),initr(y,0)],
% seq(
%     while(nenegativ(x),
%      seq(dec(x),inc(y))
%     )
%   ,inc(y)
% )
%,_).



% eval([initr(x,54)],dec(x),_).
