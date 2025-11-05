(* ::Package:: *)

(* ::Section:: *)
(*0. Package Header*)


(*problem:
\[Gamma] and Pi[n_,a_] is now derived from 1/2 F , but the rest is still with F *)
(*in our papers we use 1/2 F but it is not what emerges from Nekrasov*)


(* ::Subsection:: *)
(*Begin Package*)


BeginPackage["Nekrasov`"];


\[ScriptCapitalF]tUS0eff;


\[ScriptCapitalF]tUS22eff;


matone0;


matone22;


\[CapitalPi]B0;


\[CapitalPi]B22;


a;
u;
\[HBar];
\[CapitalLambda];
m1;
m2;
m;


(* ::Subsection::Closed:: *)
(*End public Header*)


Begin["Private`"];


(* ::Subsection::Closed:: *)
(*Auxiliary Loading*)


<<Combinatorica`


(* ::Section:: *)
(*1. General Young diagrams*)


(* ::Subsection::Closed:: *)
(*Generalities*)


(* ::Input::Initialization:: *)
DualPartition[l_]:=Module[{i},Table[Length[Select[l,(#>=i)&]],{i,1,l[[1]]}]]
DualPartition[{}]={};


(* ::Input::Initialization:: *)
get[Y_,i_]:=If[i>Length[Y],0,Y[[i]]]
arm[Y_,{i_,j_}]:=get[Y,i]-j
leg[Y_,{i_,j_}]:=get[DualPartition[Y],j]-i


(* ::Input::Initialization:: *)
boxes[Y_]:=Join@@Table[{i,j},{i,1,Length[Y]},{j,1,Y[[i]]}]


(* ::Input::Initialization:: *)
e[a_,Y1_,Y2_,s_]:=a-\[Epsilon]1 leg[Y2,s]+\[Epsilon]2(arm[Y1,s]+1)

youngPairs[k_]:=youngPairs[k]=Join@@Module[{i},Join@@Table[Outer[List,Partitions[i],Partitions[k-i],1],{i,0,k}]]


(* ::Subsection::Closed:: *)
(*Conventions 0*)


(* ::Input::Initialization:: *)
fromWa[a_,bb_,Y1_,Y2_]:=(Times@@(e[a-bb,Y1,Y2,#]&/@boxes[Y1]))(Times@@((\[Epsilon]1+\[Epsilon]2-e[-a+bb,Y2,Y1,#])&/@boxes[Y2]))

fromSU2V[a_,Y1_,Y2_]:=1/(fromWa[a,a,Y1,Y1]fromWa[a,-a,Y1,Y2]fromWa[-a,a,Y2,Y1]fromWa[-a,-a,Y2,Y2])


(* ::Input::Initialization:: *)
eigen[a_,Y_]:=(a+\[Epsilon]1(#[[1]]-1)+\[Epsilon]2(#[[2]]-1))&/@boxes[Y]
eigen[a_,Y1_,Y2_]:=eigen[a,Y1]~Join~eigen[-a,Y2]

fund[a_,Y1_,Y2_,m_]:=(Times@@((#-m+\[Epsilon]1+\[Epsilon]2)&/@eigen[a,Y1,Y2]))
antifund[a_,Y1_,Y2_,m_]:=(Times@@((#+m)&/@eigen[a,Y1,Y2]))


(* ::Subsection::Closed:: *)
(*Conventions AGH*)


(* ::Input::Initialization:: *)
fromWaAGH[a_,bb_,Y1_,Y2_]:=(Times@@(e[a-bb,Y1,Y2,#]&/@boxes[Y1]))(Times@@((e[a-bb,Y2,Y1,#])&/@boxes[Y2]))

fromSU2VAGH[a_,Y1_,Y2_]:=1/(fromWaAGH[a,a,Y1,Y1]fromWaAGH[a,-a,Y1,Y2]fromWaAGH[-a,a,Y2,Y1]fromWaAGH[-a,-a,Y2,Y2])


(* ::Input::Initialization:: *)
eigenAGH[a_,Y_,m_]:=(a+m+\[Epsilon]1(#[[1]]-1/2)+\[Epsilon]2(#[[2]]-1/2))&/@boxes[Y]
eigenAGH[a_,Y1_,Y2_,m_]:=Times@@Join[eigenAGH[a,Y1,m],eigenAGH[-a,Y2,m]]


(* ::Section:: *)
(*2. Flavours implementations*)


(* ::Subsection::Closed:: *)
(*Nf=4*)


(* ::Input::Initialization:: *)
nekrasov[n_]:=nekrasov[n]=Module[{A=youngPairs[n]},Sum[Module[{A1=A[[s]][[1]],A2=A[[s]][[2]]},fromSU2V[a ,A1,A2]antifund[a,A1,A2,m1]antifund[a,A1,A2,m2] fund[a,A1,A2,m3]fund[a,A1,A2,m4]],{s,1,Length[A]}]]


(* ::Input::Initialization:: *)
nekrasovAGH[n_]:=nekrasovAGH[n]=Module[{A=youngPairs[n]},Sum[Module[{A1=A[[s]][[1]],A2=A[[s]][[2]]},fromSU2V[a ,A1,A2]eigenAGH[a,A1,A2,m1]eigenAGH[a,A1,A2,m2]eigenAGH[a,A1,A2,m3]eigenAGH[a,A1,A2,m4]],{s,1,Length[A]}]]


(* ::Subsection:: *)
(*Nf=2*)


(* ::Input::Initialization:: *)
nekrasov2[n_]:=nekrasov2[n]=Module[{A=youngPairs[n]},Sum[Module[{A1=A[[s]][[1]],A2=A[[s]][[2]]},fromSU2V[a ,A1,A2]eigenAGH[a,A1,A2, m1]eigenAGH[a,A1,A2, m2]],{s,1,Length[A]}]]


(* ::Input::Initialization:: *)
nekrasovAGH2[n_]:=Module[{A=youngPairs[n]},Sum[Module[{A1=A[[s]][[1]],A2=A[[s]][[2]]},fromSU2VAGH[a ,A1,A2]eigenAGH[a,A1,A2,m1]eigenAGH[a,A1,A2,m2]eigenAGH[a,A1,A2,m3]eigenAGH[a,A1,A2,m4]],{s,1,Length[A]}]]


(* ::Input::Initialization:: *)
\[Gamma]2=Times[#,2]&/@(2 a Log[(2  \[HBar])/Subscript[\[CapitalLambda], 2]]+ \[HBar] Log[Gamma[1+(2 a)/\[HBar]]/Gamma[1-(2 a)/\[HBar]]]+ 1/2\[HBar] Log[Gamma[1/2+(m1- a)/\[HBar]]/Gamma[1/2+(m1+a)/\[HBar]]] +1/2\[HBar] Log[Gamma[1/2+(m2- a)/\[HBar]]/Gamma[1/2+(m2+a)/\[HBar]]]);


(* ::Input::Initialization:: *)
ruleconv22={\[Epsilon]1-> \[HBar],Subscript[\[CapitalLambda], HoldForm@2]-> Subscript[\[CapitalLambda], HoldForm@2]/2,m1->m1,m2->m2};

\[ScriptCapitalF]2tn22[N_]:=\[ScriptCapitalF]2tn22[N]=(Limit[\[Epsilon]1 \[Epsilon]2 (Series[-Log[1+Sum[Z[n] \[CapitalLambda]^(n),{n,1,N+1}]],{\[CapitalLambda],0,N}]//Normal)/.{\[CapitalLambda]->Subscript[\[CapitalLambda], HoldForm@2]^2,Z->nekrasov2},\[Epsilon]2->0]//Collect[#,Subscript[\[CapitalLambda], HoldForm@2]^2,Simplify]&)/.ruleconv22//Times[#,-1]&

\[ScriptCapitalF]tUS22[n_]:=Collect[Expand@FullSimplify[\[ScriptCapitalF]2tn22[n]/.{\[Epsilon]1->\[HBar],a->a,\!\(\*SubscriptBox[\(\[CapitalLambda]\), 
TagBox["2",
HoldForm]]\)->\!\(\*SubscriptBox[\(\[CapitalLambda]\), 
TagBox["2",
HoldForm]]\)}],\!\(\*SubscriptBox[\(\[CapitalLambda]\), 
TagBox["2",
HoldForm]]\),Simplify]

\[ScriptCapitalF]tUS22eff[n_]:=If[Head@#===Plus&&Length@#>=2,Apply[Plus,Flatten@{Simplify[\!\(\*
SubsuperscriptBox["\[CapitalLambda]", 
TagBox["2",
HoldForm], "2"]/8\)+First@#],Rest@#}],-((m1 m2 \!\(\*SubsuperscriptBox[\(\[CapitalLambda]\), 
TagBox["2",
HoldForm], \(2\)]\))/(8 a^2-2 \[HBar]^2))]&@EchoFunction[Magnify[#,0.7]&]@\[ScriptCapitalF]tUS22[n]//QuietEcho

matone22[N_]:=u==a^2- 1/2 Subscript[\[CapitalLambda], HoldForm@2]D[\[ScriptCapitalF]tUS22eff[N],Subscript[\[CapitalLambda], HoldForm@2]]

ruleUS22=Apply[Rule,matone22[2]/.{\[HBar]->0}/.\!\(\*SubscriptBox[\(\[CapitalLambda]\), 
TagBox["2",
HoldForm]]\)->\[CapitalLambda]//Expand//Collect[#,\[CapitalLambda]^2,FullSimplify]&];

ruleU2S2rv=Part[Echo@AsymptoticSolve[Equal@@ruleUS22,a,{\[CapitalLambda],0,4}],-1]//QuietEcho;

a22[n_]:=a22[n]=AsymptoticSolve[matone22[n],a,{Subscript[\[CapitalLambda], HoldForm@2],0,2n}][[2,1,2]]

\[CapitalPi]B22[n_]:=\[CapitalPi]B22[n]= ReplaceAll[Collect[D[\[ScriptCapitalF]tUS22eff[n],a],Subscript[\[CapitalLambda], HoldForm@2],Simplify]+\[Gamma]2,a->Evaluate@a22[n]]

\[CapitalPi]B22[n_/;0<=n<=3,a_]:=\[Gamma]2+Take[(*+1/2*)((4 a m1 m2 \!\(\*SubsuperscriptBox[\(\[CapitalLambda]\), 
TagBox["2",
HoldForm], \(2\)]\))/(-4 a^2+\[HBar]^2)^2)+(*1/2*)(a (256 a^8+60 m2^2 \[HBar]^6+\[HBar]^8-256 a^6 (6 m1^2+6 m2^2+\[HBar]^2)+m1^2 (-1776 m2^2 \[HBar]^4+60 \[HBar]^6)+96 a^4 (18 m2^2 \[HBar]^2+\[HBar]^4+2 m1^2 (20 m2^2+9 \[HBar]^2))-16 a^2 (36 m2^2 \[HBar]^4+\[HBar]^6+12 m1^2 (4 m2^2 \[HBar]^2+3 \[HBar]^4))) \!\(\*SubsuperscriptBox[\(\[CapitalLambda]\), 
TagBox["2",
HoldForm], \(4\)]\))/(512 (a^2-\[HBar]^2)^2 (-4 a^2+\[HBar]^2)^4)+(*1/2*)(m1 m2 (61440 a^13-8192 a^11 (14 m1^2+14 m2^2+25 \[HBar]^2)+a \[HBar]^8 (-9236 m2^2 \[HBar]^2+245 \[HBar]^4+4 m1^2 (30740 m2^2-2309 \[HBar]^2))+256 a^9 (1004 m2^2 \[HBar]^2+895 \[HBar]^4+4 m1^2 (180 m2^2+251 \[HBar]^2))+128 a^3 \[HBar]^6 (629 m2^2 \[HBar]^2-35 \[HBar]^4+m1^2 (3340 m2^2+629 \[HBar]^2))-512 a^7 (2 m2^2 \[HBar]^4+235 \[HBar]^6+2 m1^2 (120 m2^2 \[HBar]^2+\[HBar]^4))-16 a^5 (11768 m2^2 \[HBar]^6-2045 \[HBar]^8+8 m1^2 (5540 m2^2 \[HBar]^4+1471 \[HBar]^6))) \!\(\*SubsuperscriptBox[\(\[CapitalLambda]\), 
TagBox["2",
HoldForm], \(6\)]\))/(384 (-4 a^2+\[HBar]^2)^6 (4 a^4-13 a^2 \[HBar]^2+9 \[HBar]^4)^2),n]



(* ::Subsection:: *)
(*Nf=0*)


(* ::Input::Initialization:: *)
nekrasov0[n_]:=nekrasov0[n]=Module[{A=youngPairs[n]},Sum[Module[{A1=A[[s]][[1]],A2=A[[s]][[2]]},fromSU2V[a ,A1,A2]],{s,1,Length[A]}]]


(* ::Input::Initialization:: *)
\[ScriptCapitalF]0tn[N_]:=\[ScriptCapitalF]0tn[N]=(Limit[\[Epsilon]1 \[Epsilon]2 (Series[-Log[1+Sum[Z[n] \[CapitalLambda]^(n),{n,1,N+1}]],{\[CapitalLambda],0,N}]//Normal)/.{\[CapitalLambda]->Subscript[\[CapitalLambda], HoldForm@0]^4,Z->nekrasov0},\[Epsilon]2->0]//Collect[#,Subscript[\[CapitalLambda], HoldForm@0]^2,Simplify]&)/.ruleconv0//Times[#,-1]&
\[ScriptCapitalF]tUS0[n_]:=Collect[Expand@FullSimplify[\[ScriptCapitalF]0tn[n]/.{\[Epsilon]1->\[HBar],a->a}],Subscript[\[CapitalLambda], HoldForm@0],Simplify]
\[ScriptCapitalF]tUS0eff[n_]:=\[ScriptCapitalF]tUS0[n]//QuietEcho


(* ::Input::Initialization:: *)
ruleconv0={\[Epsilon]1-> \[HBar],Subscript[\[CapitalLambda], HoldForm@0]-> Subscript[\[CapitalLambda], HoldForm@0]/Sqrt@2}



(* ::Input::Initialization:: *)
matone0[N_]:=u==a^2- 1/4 Subscript[\[CapitalLambda], HoldForm@0]D[\[ScriptCapitalF]tUS0eff[N],Subscript[\[CapitalLambda], HoldForm@0]]//Collect[#,Subscript[\[CapitalLambda], HoldForm@0],Simplify]&

ruleUS0=RuleDelayed@@(matone0[2]/.\[HBar]:>0);


(* ::Input::Initialization:: *)
\[Gamma]0=Times[#,2]&/@(4 a Log[(Sqrt[2]\[HBar])/Subscript[\[CapitalLambda], HoldForm@0]]+ \[HBar] Log[Gamma[1+(2 a)/\[HBar]]/Gamma[1-(2 a)/\[HBar]]]);


(*factor 2 normalization*)


(* ::Input::Initialization:: *)
\[CapitalPi]B0[n_/;0<=n<=3,a_]:=\[Gamma]0+Take[(*1/2*)(4 a \!\(\*SubsuperscriptBox[\(\[CapitalLambda]\), 
TagBox["0",
HoldForm], \(4\)]\))/(-4 a^2+\[HBar]^2)^2+(*1/2*)(3 a (80 a^4-16 a^2 \[HBar]^2-37 \[HBar]^4) \!\(\*SubsuperscriptBox[\(\[CapitalLambda]\), 
TagBox["0",
HoldForm], \(8\)]\))/(32 (a^2-\[HBar]^2)^2 (-4 a^2+\[HBar]^2)^4)+(*1/2*)(5 (2304 a^9-1536 a^7 \[HBar]^2-8864 a^5 \[HBar]^4+5344 a^3 \[HBar]^6+1537 a \[HBar]^8) \!\(\*SubsuperscriptBox[\(\[CapitalLambda]\), 
TagBox["0",
HoldForm], \(12\)]\))/(24 (-4 a^2+\[HBar]^2)^6 (4 a^4-13 a^2 \[HBar]^2+9 \[HBar]^4)^2),n]


(* ::Section:: *)
(*-1. Package Footer*)


End[];
EndPackage[];
