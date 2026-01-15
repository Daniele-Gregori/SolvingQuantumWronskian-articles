(* ::Package:: *)

(* ::Title:: *)
(*Nekrasov Functions*)


(* ::Author:: *)
(*Daniele Gregori, with open code by Yuji Tachikawa*)


(* ::Section:: *)
(*0. Package Header*)


(* ::Subsection::Closed:: *)
(*Begin Package*)


BeginPackage["Nekrasov`"];


NekrasovF0;
NekrasovF2;
NekrasovF3;
NekrasovF4;


Matone0;
Matone2;
Matone3;


NekrasovAD0;
NekrasovAD2;
NekrasovAD3;


a;
u;
Subscript[\[CapitalLambda], 0];
Subscript[\[CapitalLambda], 1];
Subscript[\[CapitalLambda], 2];
Subscript[\[CapitalLambda], 3];
q;
\[HBar];
Subscript[\[Epsilon], 1];
Subscript[\[Epsilon], 2];
m1;
m2;
m3;
m4;


(* ::Subsection::Closed:: *)
(*End public Header*)


Begin["Private`"];


(* ::Section:: *)
(*1. NekrasovF definition*)


(* ::Subsection::Closed:: *)
(*Young diagrams (Tachikawa)*)


(* ::Subsubsection:: *)
(*dual (or transposed) partition*)


(* ::Input::Initialization:: *)
DualPartition[l_]:=Table[Length[Select[l,(#>=i)&]],{i,1,l[[1]]}]
DualPartition[{}]={};


(* ::Subsubsection:: *)
(*arm and leg lengths*)


(* ::Input::Initialization:: *)
get[Y_,i_]:=If[i>Length[Y],0,Y[[i]]]
arm[Y_,{i_,j_}]:=get[Y,i]-j
leg[Y_,{i_,j_}]:=get[DualPartition[Y],j]-i
e[a_,Y1_,Y2_,s_]:=a-Subscript[\[Epsilon], 1]  leg[Y2,s] + Subscript[\[Epsilon], 2] (arm[Y1,s]+1)


(* ::Input::Initialization:: *)
boxes[Y_]:=Join@@Table[Table[{i,j},{j,1,Y[[i]]}],{i,1,Length[Y]}]


(* ::Subsubsection:: *)
(*Pairs*)


(* ::Input::Initialization:: *)
ClearAll[youngPairs]
youngPairs[k_]:=youngPairs[k]=Join@@ Identity[Join@@ Table[Outer[List,IntegerPartitions[i],IntegerPartitions[k-i],1],{i,0,k}]]


(* ::Subsubsection:: *)
(*Tuples*)


(* ::Input::Initialization:: *)
YoungTuples[1,tot_]:={#}& /@IntegerPartitions[tot]
YoungTuples[n_,tot_]:= YoungTuples[n,tot]=Flatten[Table[Flatten[ Outer[Prepend[#2,#1]&,IntegerPartitions[r],YoungTuples[n-1,tot-r],1,1],1],{r,0,tot}],1]


(* ::Subsection::Closed:: *)
(*Particles SU(2)*)


(* ::Subsubsection:: *)
(*Gauge (Tachikawa)*)


(* ::Text:: *)
(*Contribution of a W-boson*)


(* ::Input::Initialization:: *)
fromWa[a_,bb_,Y1_,Y2_]:=(Times @@ ( (e[a-bb,Y1,Y2,#](Subscript[\[Epsilon], 1]+Subscript[\[Epsilon], 2]-e[a-bb,Y1,Y2,#]))&/@ boxes[Y1]))


(* ::Text:: *)
(*Contribution of a U(2) vector multiplet*)


(* ::Input::Initialization:: *)
fromSU2V[a_,Y1_,Y2_]:=1/(fromWa[a,a,Y1,Y1]fromWa[a,-a,Y1,Y2]fromWa[-a,a,Y2,Y1]fromWa[-a,-a,Y2,Y2])


(* ::Subsubsection:: *)
(*Matter*)


\[Phi][a_,Y_]:=(a+Subscript[\[Epsilon], 1](#[[1]]-1)+Subscript[\[Epsilon], 2](#[[2]]-1))&/@boxes[Y]


(* ::Input::Initialization:: *)
fund[a_,Y1_,Y2_,m_]:=
Times[
Times@@Map[#-m+Subscript[\[Epsilon], 1]+Subscript[\[Epsilon], 2]&,\[Phi][a,Y1]],
Times@@Map[#-m+Subscript[\[Epsilon], 1]+Subscript[\[Epsilon], 2]&,\[Phi][-a,Y2]]]
antifund[a_,Y1_,Y2_,m_]:=fund[a,Y1,Y2,Subscript[\[Epsilon], 1]+Subscript[\[Epsilon], 2]-m]


(* ::Subsection::Closed:: *)
(*Partitions functions*)


(* ::Input::Initialization:: *)
assocCoupling=AssociationThread[{"SU2"},{AssociationThread[{0,1,2,3,4,All},{Subscript[\[CapitalLambda], 0]^4,Subscript[\[CapitalLambda], 1]^3,Subscript[\[CapitalLambda], 2]^2,Subscript[\[CapitalLambda], 3],q,q}]}];


(* ::Input::Initialization:: *)
ascFactors=AssociationThread[{"SU2"},{Association@Join[#->(2^(-1/(2-#/2)))^(4-#)&/@Range[0,3],{4->1/4,All->1/4}]}];


(* ::Input::Initialization:: *)
ClearAll[nekrasovSU2Nf]
nekrasovSU2Nf[n_,k_]:=
nekrasovSU2Nf[n,k]=
Plus@@Map[fromSU2V[a ,#[[1]],#[[2]]]Times@@Take[Unevaluated@{antifund[a,#[[1]],#[[2]],m1],antifund[a,#[[1]],#[[2]],m2] ,fund[a,#[[1]],#[[2]],m3],fund[a,#[[1]],#[[2]],m4]},k]&,youngPairs[n]]


(* ::Input::Initialization:: *)
(*to understand better*)
(*seems to be due to definition A.9 of AGH*)
(*maybe it is also related to the U(1) factor*)
convAGH={m1->m1+Subscript[\[Epsilon], 1]/2+Subscript[\[Epsilon], 2]/2,m2->m2+Subscript[\[Epsilon], 1]/2+Subscript[\[Epsilon], 2]/2,m3->-m3+Subscript[\[Epsilon], 1]/2+Subscript[\[Epsilon], 2]/2,m4->-m4+Subscript[\[Epsilon], 1]/2+Subscript[\[Epsilon], 2]/2};


(* ::Subsection::Closed:: *)
(*Main definition*)


(* ::Input::Initialization:: *)
ClearAll[NekrasovF,NekrasovZ]
Options[NekrasovF]={"GaugeGroup"->"SU2","MatterFlavors"->All,"InstantonOrder"->Automatic,"OmegaBackground"->"Full","SimplifyResult"->Automatic,"Compile"->Automatic,"Conventions"->"AGH","U1Factor"->False};

NekrasovZ[opt:OptionsPattern[NekrasovF]]:=
Block[{n,Nf,simpopt,c,core,back},
n=OptionValue["InstantonOrder"]/.Automatic->1;
Nf=OptionValue["MatterFlavors"];
simpopt=OptionValue["SimplifyResult"]/.Automatic->True;
c=assocCoupling[OptionValue["GaugeGroup"]][Nf];
core=Which[OptionValue["GaugeGroup"]=="SU2",
			Plus@@
			Table[nekrasovSU2Nf[i,Nf]c^i,{i,1,n}]
				/.convAGH];
core=If[OptionValue["Conventions"]==="AGH",core/.convAGH,core];
If[simpopt,Collect[core,c,Simplify],core]]


NekrasovF[opt:OptionsPattern[NekrasovF]]:=
Block[{n,Zn,Z,Nf,gau,c,r,back,coeff1,u1,simpopt,simp},
n=OptionValue["InstantonOrder"]/.Automatic->1;
Nf=OptionValue["MatterFlavors"];
gau=OptionValue["GaugeGroup"];
c=assocCoupling[gau][Nf]
	/.Subscript[x_,y_]:>Symbol[ToString[x]<>ToString[y]]
		/.Power[x_,y_]:>Symbol[ToString[x]<>ToString[y]];
r=ascFactors[gau][Nf];
Zn[k_]:=Which[gau==="SU2",nekrasovSU2Nf[k,Nf]];
Zn[0]=1;
Z=Normal@Series[
	-Log[Sum[Zn[k](r c)^k,{k,0,n}]],
		{c,0,n}];
Z=If[OptionValue["Conventions"]==="AGH",Z/.convAGH,Z];
back=Switch[OptionValue["OmegaBackground"],
				"Full",
				Subscript[\[Epsilon], 1] Subscript[\[Epsilon], 2]Z,
				"NS",
				Limit[Subscript[\[Epsilon], 1] Subscript[\[Epsilon], 2]Z,Subscript[\[Epsilon], 2]->0]];
coeff1=Coefficient[back,c,1];
u1=If[!OptionValue["U1Factor"]&&OptionValue["Conventions"]==="AGH",
		back-coeff1 c+Plus@@Discard[List@@Apart[coeff1,a],FreeQ[#,a]&]c,
		back];
simpopt=OptionValue["SimplifyResult"]/.Automatic->True;
simp=If[simpopt,Collect[u1,c,Simplify],u1];
simp/.c->assocCoupling[OptionValue["GaugeGroup"]][Nf]]


(* ::Section:: *)
(*2. Derived definitions*)


(* ::Subsection::Closed:: *)
(*NekrasovFk*)


NekrasovF0[n_]:=NekrasovF0[n]=
	NekrasovF["InstantonOrder"->n,"MatterFlavors"->0,"OmegaBackground"->"NS"](*/.Subscript[\[Epsilon], 1]-> I \[HBar]/.a->I a*)


NekrasovF2[n_]:=NekrasovF2[n]=
	NekrasovF["InstantonOrder"->n,"MatterFlavors"->2,"OmegaBackground"->"NS"](*/.Subscript[\[Epsilon], 1]-> I \[HBar]/.a->I a*)


NekrasovF3[n_]:=NekrasovF3[n]=
	NekrasovF["InstantonOrder"->n,"MatterFlavors"->3,"OmegaBackground"->"NS"](*/.Subscript[\[Epsilon], 1]-> I \[HBar]/.a->I a*)


NekrasovF4[n_]:=NekrasovF4[n]=
	NekrasovF["InstantonOrder"->n,"MatterFlavors"->4,"OmegaBackground"->"NS","U1Factor"->True](*/.Subscript[\[Epsilon], 1]-> I \[HBar]/.a->I a*)


(* ::Subsection:: *)
(*NekrasovADk*)


(* ::Subsubsection::Closed:: *)
(*Perturbative part*)


\[Gamma]0=Times[#,-2]&/@
	(4 a Log[(Sqrt[2]\[HBar])/Subscript[\[CapitalLambda], 0]]+ \[HBar] Log[Gamma[1+(2 a)/\[HBar]]/Gamma[1-(2 a)/\[HBar]]]);


\[Gamma]2=Times[#,-2]&/@
		(2 a Log[(2  \[HBar])/Subscript[\[CapitalLambda], 2]]+ \[HBar] Log[Gamma[1+(2 a)/\[HBar]]/Gamma[1-(2 a)/\[HBar]]]
		+ 1/2\[HBar] Log[Gamma[1/2+(m1- a)/\[HBar]]/Gamma[1/2+(m1+a)/\[HBar]]] +1/2\[HBar] Log[Gamma[1/2+(m2- a)/\[HBar]]/Gamma[1/2+(m2+a)/\[HBar]]]);


\[Gamma]3=Times[#,-2]&/@
		(1 a Log[(4  \[HBar])/Subscript[\[CapitalLambda], 3]]+\[HBar] Log[Gamma[1+(2 a)/\[HBar]]/Gamma[1-(2 a)/\[HBar]]]
		+1/2 \[HBar] Log[Gamma[1/2+(m1- a)/\[HBar]]/Gamma[1/2+(m1+a)/\[HBar]]] +1/2\[HBar] Log[Gamma[1/2+(m2- a)/\[HBar]]/Gamma[1/2+(m2+a)/\[HBar]]] +1/2\[HBar] Log[Gamma[1/2+(m3- a)/\[HBar]]/Gamma[1/2+(m3+a)/\[HBar]]]);


(* ::Subsubsection::Closed:: *)
(*Full AD*)


NekrasovAD0[n_]:=NekrasovAD0[n]= 
	Collect[D[NekrasovF0[n],a],Subscript[\[CapitalLambda], 0],Simplify]+\[Gamma]0


NekrasovAD2[n_]:=NekrasovAD2[n]= 
	Collect[D[NekrasovF2[n],a],Subscript[\[CapitalLambda], 2],Simplify]+\[Gamma]2


NekrasovAD3[n_]:=NekrasovAD3[n]= 
	Collect[D[NekrasovF3[n],a],Subscript[\[CapitalLambda], 3],Simplify]+\[Gamma]3


(* ::Subsection::Closed:: *)
(*Matonek*)


Matone0[n_]:=Matone0[n]=
	u==a^2+1/4 Subscript[\[CapitalLambda], 0]D[NekrasovF0[n],Subscript[\[CapitalLambda], 0]]


Matone2[n_]:=Matone2[n]=
	u==a^2+ 1/2 Subscript[\[CapitalLambda], 2]D[NekrasovF2[n],Subscript[\[CapitalLambda], 2]]


Matone3[n_]:=Matone3[n]=
	u==a^2+  Subscript[\[CapitalLambda], 3]D[NekrasovF3[n],Subscript[\[CapitalLambda], 3]]


(* ::Section:: *)
(*-1. Package Footer*)


End[];
EndPackage[];
