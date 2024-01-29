(* ::Package:: *)

BeginPackage["TranscendentalProblems`"];


TrigExtCanonicalForm::usage="Canonical Form of f\[Element]S[sin x,cos x]";


TrigExtVerify::usage="Verify a closed FO formula";


Begin["Private`"];


TrigExtCanonicalForm[f_,x_]:=Module[{ret},ret:=f;ret=ret/.{Sin[x]->(2Tan[x/2])/(1+Tan[x/2]^2),Cos[x]-> (1-Tan[x/2]^2)/(1+Tan[x/2]^2)};Return[Together[ret]]];


GetBound[f_,y_,x_,tau_:15/16]:=Module[{N0,N1,M0,M1,lc,subres,subrespoly,l,g,hp,hm,realroots},
	lc=Coefficient[f,y,Exponent[f,y]];
	(*subres=Subresultants[f,D[f,y],y];*)

	subrespoly=SubresultantPolynomials[f,D[f,y],y];
	subres=Simplify[SelectFirst[subrespoly,#=!=0&]];
	(*Delineable Bound*)
	realroots=Join[{{x->0}},Solve[lc==0,x,Reals],Solve[Coefficient[subres,y,Exponent[subres,y]]==0,x,Reals]];
	M0=Max@@(x/.realroots);
	N0=Min@@(x/.realroots);
	g=Numerator[Together[PolynomialQuotient[f,subres,y]]];
	
	(*Derivative Bound*)
	hp=2*D[g,x]+tau*D[g,y]*(y^2+1);
	hm=2*D[g,x]-tau*D[g,y]*(y^2+1);
	realroots=Join[{{x-> 0}},Solve[SelectFirst[Subresultants[hp,g,y],#=!=0&]==0,x,Reals],Solve[SelectFirst[Subresultants[hm,g,y],#=!=0&]==0,x,Reals]];
	M1=Max@@(x/.realroots);
	N1=Min@@(x/.realroots);
	Print["Subresultant Polynomial=",Simplify[subres],", Square-free part=",Simplify[g],", Delineable Bound=",M0,", CM Bound=",M1,"."];
	Print["\!\(\*SubscriptBox[\(h\), \(+\)]\)=",Simplify[hp]," ;\!\(\*SubscriptBox[\(h\), \(-\)]\)=",Simplify[hm],"."];
	Return[{Min[N0,N1],Max[M0,M1]}];
];


TrigExtExtract[exp_]:=Module[{},
	If[(exp[[0]]==Implies)||(exp[[0]]==And)||(exp[[0]]==Or||exp[[0]]==Xor||exp[[0]]==Equivalent),Return[Join@@Table[TrigExtExtract[exp[[i]]],{i,Length[exp]}]]];
	If[(exp[[0]]==Not),Return[TrigExtExtract[exp[[1]]]]];
	Return[{exp}];
];


TrigExtExpressionPreprocess[exp0_]:=Module[{exp,repOps,ret,mtps,bv,var,flag},
	exp=exp0[[2]];
	repOps=Alternatives@@{LessEqual,GreaterEqual,Less,Greater,Equal,Unequal};
	ret=exp/.op_[a_,b_]/;MatchQ[op,repOps]:>op[a-b,0];
	mtps=DeleteDuplicates[TrigExtExtract[(ret)/.op_[a_,0]/;MatchQ[op,repOps]:>a]];
	bv=Array[b,Length[mtps]];
	ret=ret/.Table[mtps[[i]]-> bv[[i]],{i,Length[mtps]}];
	var=exp0[[1]];
	If[exp0[[0]]==Exists,flag=False,flag=True,flag=True];
	(*Print[ret,",",bv,",",mtps,",",var,",",flag];*)
	Return[{ret,bv,mtps,var,flag}];
];


TrigExtVerify[exp0_]:=Module[{exp,repOps,ret,trigexts,prod,x,y,M1,N1,B0,B1,realroots,oddpi,kn,kp,t,i},
	exp=exp0[[2]];
	x:=exp0[[1]];
	repOps=Alternatives@@{LessEqual,GreaterEqual,Less,Greater,Equal,Unequal};
	ret=exp/.op_[a_,b_]/;MatchQ[op,repOps]:>op[a-b,0];
	trigexts=DeleteDuplicates[TrigExtExtract[(ret)/.op_[a_,0]/;MatchQ[op,repOps]:>a]];
	Print["Parse result: ",trigexts];
	prod=Times@@trigexts;
	Print["Product= ",prod];
	{N1,M1}=GetBound[(Times@@Table[(Numerator[TrigExtCanonicalForm[trigexts[[i]],x]]),{i,1,Length[trigexts]}])/.{Tan[x/2]->y},y,x];
	B0=0;B1=0;
	For[i=1,i<=Length[trigexts],i++,
		If[Simplify[trigexts[[i]]/.{Sin[x]->0,Cos[x]->-1}]=!=0,
			realroots=Join[{{x->B0},{x->B1}},Solve[(trigexts[[i]]/.{Sin[x]->0,Cos[x]->-1})==0,x,Reals]];
			B0=Min@@(x/.realroots); B1==Max@@(x/.realroots);
		]
	];
	Print["B0= ",B0,", B1= ",B1," ; N1= ",N1," M1= ",M1];
	B0=Min[B0,N1]; B1=Max[B1,M1];
	kn=Ceiling[B0/(2*Pi)-1/2]-1; kp=Floor[B1/(2*Pi)+1/2]+1;
	Print["\!\(\*SubscriptBox[\(k\), \(-\)]\)=",kn,", \!\(\*SubscriptBox[\(k\), \(+\)]\)=",kp];
	If[exp0[[0]]===Exists,
		ret=Exists[t,Floor[(2*kn-1)*Pi]<=t<=Ceiling[(2*kp+1)*Pi],exp/.{x->t}];
		Return[Reduce[ret,t,Reals]],
		ret=Exists[t,Floor[(2*kn-1)*Pi]<=t<=Ceiling[(2*kp+1)*Pi],Not[exp]/.{x->t}];
		Return[Not[Reduce[ret,t,Reals]]]
	];
	Print[ret];
	Return[Reduce[ret,t,Reals]];
]


End[];


EndPackage[];
