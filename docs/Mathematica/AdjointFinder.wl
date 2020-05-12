(* ::Package:: *)

BeginPackage["AdjointFinder`"];
(* AdjointFinder: If you use this in your research or teaching, please cite the webpage: 
https://gokulhari.github.io/webpage/AdjointFinder.html
and the paper:
G.Hariharan, S.Kumar, and M.R.Jovanovic, Well-conditioned ultraspherical and spectral integration methods for resolvent analysis of channel flows of Newtonian and viscoelastic fluids, Phys.Rev.Fluids, 2020, note:Submitted}

Written by Gokul
*)


ComputeAd::usage = "Computes the formal adjoint of an operator wrt L2[a,b] inner product,
eqn_ad = ComputeAd[eqns,{y,a,b},{vars,order}]. Inputs are the differential equations, 
independent variable with domain y \[Element] [a,b], and the list of 
dependent variables, and the overall order of the differential system.";
Computebc::usage = "Computes the adjoint boundary conditions wrt L2[a,b] inner
product. Inputs are the differential equations, 
the left boundary conditions, the right boundary conditions, and independent variable with domain y \[Element] [a,b], and the list of 
dependent variables, and the overall order of the differential system." ;
Adjoint::usage = "This function computes adjoints and adjoint boundary conditions wrt. L2[a,b] inner
product. {eqns_ad,bc_ad} = Adjoints[eqns,lbc,rbc,{y,a,b},{vars, order}]. Inputs are the differential equations, 
the left boundary conditions, the right boundary conditions, and independent variable with domain y \[Element] [a,b], and the list of 
dependent variables, and the overall order of the differential system.";


Begin["`Private`"];


ComputeAd[eqns_,var_,invar_]:=Module[{eqn = eqns,var1 = var,invar1=invar},
n = Dimensions[eqn][[1]];(*Number of equations*)
nu = Dimensions[invar1][[1]] - 1; (*Number of unknowns*)
(*For non-square matrices, number of equations can be different from unknowns*)
Do[alpha[k]=Table[Coefficient[eqn[[i]],D[invar1[[j]][var1[[1]] ],{var1[[1]],k}]],{i,n},{j,nu}],{k,0,Last[invar1]}];
Do[beta[i] = Sum[(-1)^j Binomial[j,i] D[alpha[j],{var1[[1]],j-i}],{j,i,Last[invar1]}],{i,0,Last[invar1]}];
Do[beta[i] = ComplexExpand[ConjugateTranspose[beta[i]]],{i,0,Last[invar1]}];
eqnAdjoint = ConstantArray[0,n];
gs =Table[invar1[[i]][var1[[1]]],{i,nu}];
(*Print[beta[1]];*)
If[n>= nu,eqnAdjoint = Sum[beta[i].D[gs,{var1[[1]],i}],{i,0,Last[invar1]}],eqnAdjoint = Sum[D[gs,{var1[[1]],i}].beta[i],{i,0,Last[invar1]}]];
Clear[alpha,beta];
Flatten[eqnAdjoint]
];


Computebc[eqns_,lbc_,rbc_,var_,invar_]:=Module[{eqn = eqns, lbc1 = lbc,rbc1=rbc,var1 = var,invar1=invar},
n = Dimensions[eqn][[1]];(*Number of equations*)
nlbc = Dimensions[lbc1][[1]];(*Number of equations*)
nrbc = Dimensions[rbc1][[1]];(*Number of equations*)
Do[alpha[k]=Table[Coefficient[eqn[[i]],D[invar1[[j]][var1[[1]] ],{var1[[1]],k}]],{i,n},{j,n}],{k,0,Last[invar1]}]
Do[beta[i] = Sum[(-1)^j Binomial[j,i] D[alpha[j],{var1[[1]],j-i}],{j,i,Last[invar1]}],{i,0,Last[invar1]}];
Do[beta[i] = ComplexExpand[ConjugateTranspose[beta[i]]],{i,0,Last[invar1]}];
eqnAdjoint = ConstantArray[0,n];
gs =Table[invar1[[i]][var1[[1]]],{i,n}];
eqnAdjoint = Sum[beta[i].D[gs,{var1[[1]],i}],{i,0,n}];
Do[Do[Cmat[i][j] = Table[0,{i,n},{j,n}],{i,0,Last[invar1]-1}],{j,0,Last[invar1]-1}];
Do[Cmat[i][j]=Sum[(-1)^k Binomial[k,i] D[alpha[k + j + 1],{var1[[1]],k-i}],{k,i,Last[invar1]-j}],{i,0,Last[invar1]-1},{j,0,Last[invar1]-i-1}];
Amat = ArrayFlatten[Table[Cmat[i][j],{i,0,Last[invar1]-1},{j,0,Last[invar1]-1}]];
(*Print[MatrixForm[Amat]];*)
lbcmat = ConstantArray[0,{nlbc,Last[invar1]*n}];
rbcmat = ConstantArray[0,{nrbc,Last[invar1]*n}];
(*Print[ Coefficient[lbcmat[[1]],D[invar1[[1]][var1[[1]] ],{var1[[1]],1}]/.var1[[1]]\[Rule] var1[[2]]]];*)
Do[
m=1;Do[Do[lbcmat[[i,m]] =  Coefficient[lbc1[[i]],D[invar1[[j]][var1[[1]] ],{var1[[1]],k}]/.var1[[1]]-> var1[[2]]];(*Print[{i,m,lbcmat[[i,m]]}];*)m=m+1,{j,n}],{k,0,Last[invar1]-1}],{i,nlbc}];
Do[
m=1;Do[Do[rbcmat[[i,m]] =  Coefficient[rbc1[[i]],D[invar1[[j]][var1[[1]] ],{var1[[1]],k}]/.var1[[1]]-> var1[[3]]];(*Print[{i,m,rbcmat[[i,m]]}];*)m=m+1,{j,n}],{k,0,Last[invar1]-1}],{i,nrbc}];
(*Print[lbcmat];*)
nsplbc1 = Transpose[NullSpace[lbcmat]];
finallbc1 = Transpose[(Amat.nsplbc1)];
nsprbc1 = Transpose[NullSpace[rbcmat]];
finalrbc1 = Transpose[(Amat.nsprbc1)];
lbcvarmat = ConstantArray[0,Last[invar1]*n];
rbcvarmat = ConstantArray[0,Last[invar1]*n];

m=1;Do[Do[lbcvarmat[[m]] = D[invar1[[j]][var1[[1]] ],{var1[[1]],k}]/.var1[[1]]-> var1[[2]];(*Print[{i,m,rbcmat[[i,m]]}];*)m=m+1,{j,n}],{k,0,Last[invar1]-1}];

m=1;Do[Do[rbcvarmat[[m]] = D[invar1[[j]][var1[[1]] ],{var1[[1]],k}]/.var1[[1]]-> var1[[3]];(*Print[{i,m,rbcmat[[i,m]]}];*)m=m+1,{j,n}],{k,0,Last[invar1]-1}];
lbc2 = ( finallbc1.lbcvarmat)/.{var1[[1]]-> var1[[2]]};
rbc2 =  (finalrbc1.rbcvarmat)/.{var1[[1]]-> var1[[3]]};
Clear[alpha,beta,Cmat];
Flatten[{lbc2,rbc2}]
];


Adjoint[eqns_,lbc_,rbc_,var_,invar_]:= {ComputeAd[eqns,var,invar],Computebc[eqns,lbc, rbc,var,invar]};


End[];


EndPackage[];
