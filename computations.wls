#!/usr/bin/env wolframscript
(* ::Package:: *)

(* ::Title:: *)
(*Computer Algebra Codes:*)
(*Bifurcation analysis of waning-boosting epidemiological models with repeat infections and varying immunity periods *)


(* ::Subtitle:: *)
(*Symbolic computations : Disease Free Equilibrium, Endemic Equilibrium, Routh-Hurwitz Criterion*)


ClearAll["Global`*"];


On[Solve::svars];


(* ::Chapter:: *)
(*Preliminaries*)


(* ::Section::Closed:: *)
(*System description*)


Seq = -\[Beta] * (Istar + Jstar * \[Xi]) * Sstar + \[Omega] * \[Kappa] * Wstar + \[Mu] * (1 - Sstar);
Ieq =  \[Beta] * (Istar + Jstar * \[Xi]) * Sstar - \[Gamma] * Istar - \[Mu] * Istar;
Weq = \[Alpha] * \[Kappa] * (1 - Sstar - Istar - Wstar - Jstar) - \[Omega] * \[Kappa] * Wstar - \[Beta] * \[Nu] * (Istar + \[Xi] * Jstar) * Wstar - \[Mu] * Wstar;
Jeq = \[Nu] * \[Beta] * (Istar + \[Xi] * Jstar) * Wstar - \[Mu] * Jstar - \[Rho] * Jstar;


(* ::Section::Closed:: *)
(*Parameters*)


(* ::Text:: *)
(*We are mainly considering parametrizations avoiding extreme cases. Nevertheless, we list the conservative parameter regions below.*)


parameterAssumptions = {
	\[Beta] > 0,
	\[Xi] >= 0,
	\[Gamma] > 0,
	\[Rho] > 0,
	\[Nu] > 0,
	\[Kappa] > 0,
	\[Omega] > 1,
	\[Alpha] > 1,
	\[Mu] > 0
};
parameterAssumptions // TableForm


(* ::Chapter:: *)
(*Equilibria*)


(* ::Text:: *)
(*Our goal is twofold when finding equilibria of the system. We are interested in finding all equilibria (mathematically) and finding all with epidemiological feasibility (values and total sum inside [0, 1])*)


(* ::Section::Closed:: *)
(*Case \[Xi] = 0*)


(* ::Text:: *)
(*We now assume that the secondary infections are not infectious.*)


(* ::Subsection::Closed:: *)
(*I* = 0 (Disease Free Equilibrium)*)


(* ::Subsubsection::Closed:: *)
(*I**)


I\[Ellipsis]corner\[Ellipsis]dfe = 0


Ieq /. {\[Xi] -> 0}


Ieq /. {\[Xi] -> 0, Istar -> I\[Ellipsis]corner\[Ellipsis]dfe}


(* ::Subsubsection::Closed:: *)
(*J**)


Jeq /. {\[Xi] -> 0, Istar -> I\[Ellipsis]corner\[Ellipsis]dfe}


(* ::Text:: *)
(*As \[Mu] + \[Rho] > 0, we have that*)


J\[Ellipsis]corner\[Ellipsis]dfe = 0


(* ::Subsubsection::Closed:: *)
(*W**)


Weq /. {\[Xi] -> 0, Istar -> I\[Ellipsis]corner\[Ellipsis]dfe, Jstar -> J\[Ellipsis]corner\[Ellipsis]dfe}


Seq /. {\[Xi] -> 0, Istar -> I\[Ellipsis]corner\[Ellipsis]dfe, Jstar -> J\[Ellipsis]corner\[Ellipsis]dfe}


dfeCalc1 = Solve[Seq == 0 /. {\[Xi] -> 0, Istar -> I\[Ellipsis]corner\[Ellipsis]dfe, Jstar -> J\[Ellipsis]corner\[Ellipsis]dfe}, Sstar]


Simplify[Weq /. Join[{\[Xi] -> 0, Istar -> I\[Ellipsis]corner\[Ellipsis]dfe, Jstar -> J\[Ellipsis]corner\[Ellipsis]dfe}, First[dfeCalc1]]]


(* ::Text:: *)
(*As (\[Alpha] \[Kappa]+\[Mu]), (\[Mu]+\[Kappa] \[Omega]), \[Mu] > 0, we have that *)


W\[Ellipsis]corner\[Ellipsis]dfe = 0


(* ::Subsubsection::Closed:: *)
(*S**)


Seq /. {\[Xi] -> 0, Istar -> I\[Ellipsis]corner\[Ellipsis]dfe, Jstar -> J\[Ellipsis]corner\[Ellipsis]dfe, Wstar -> W\[Ellipsis]corner\[Ellipsis]dfe}


(* ::Text:: *)
(*As \[Mu] > 0, we have that *)


S\[Ellipsis]corner\[Ellipsis]dfe = 1


(* ::Subsubsection::Closed:: *)
(*Result*)


(* ::Text:: *)
(*Clearly the obtained equilibrium is epidemiologically feasible*)


{
Sstar -> S\[Ellipsis]corner\[Ellipsis]dfe,
Istar -> I\[Ellipsis]corner\[Ellipsis]dfe,
Jstar -> J\[Ellipsis]corner\[Ellipsis]dfe,
Wstar -> W\[Ellipsis]corner\[Ellipsis]dfe
} // TableForm


(* ::Subsection::Closed:: *)
(*Equilibria with I* != 0*)


(* ::Subsubsection::Closed:: *)
(*S**)


Ieq /. {\[Xi] -> 0}


Simplify[(Ieq /. {\[Xi] -> 0}) / Istar]


eeCalc1 = Solve[(Ieq /. {\[Xi] -> 0}) / Istar == 0, Sstar]


S\[Ellipsis]corner\[Ellipsis]ee = Sstar /. First[eeCalc1]


(* ::Text:: *)
(*Clearly, for epidemiological relevance, we need that \[Beta] >= \[Gamma] + \[Mu]*)


(* ::Subsubsection::Closed:: *)
(*I**)


Seq /. {\[Xi] -> 0, Sstar -> S\[Ellipsis]corner\[Ellipsis]ee}


eeCalc2 = Simplify[Solve[(Seq /. {\[Xi] -> 0, Sstar -> S\[Ellipsis]corner\[Ellipsis]ee}) == 0, Istar]]


(* ::Text:: *)
(*Clearly, if W* >= 0 and \[Beta] >= \[Gamma] + \[Mu]      (needed for epidem. feas. of W* and S*), then I* >= 0.*)


I\[Ellipsis]corner\[Ellipsis]ee = Istar /. First[eeCalc2]


(* ::Subsubsection::Closed:: *)
(*J**)


Simplify[Jeq /. {\[Xi] -> 0, Sstar -> S\[Ellipsis]corner\[Ellipsis]ee, Istar -> I\[Ellipsis]corner\[Ellipsis]ee}]


eeCalc3 = Expand[Solve[(Simplify[Jeq /. {\[Xi] -> 0, Sstar -> S\[Ellipsis]corner\[Ellipsis]ee, Istar -> I\[Ellipsis]corner\[Ellipsis]ee}]) == 0, Jstar]]


(* ::Text:: *)
(*Clearly, if W* >= 0 and \[Beta] >= \[Gamma] + \[Mu]      (needed for epidem . rel . of W* and S*), then J* >= 0.*)


J\[Ellipsis]corner\[Ellipsis]ee = Wstar * \[Nu] * (\[Mu] * (\[Beta] - \[Gamma] - \[Mu]) + Wstar * \[Beta] * \[Kappa] * \[Omega])/ ((\[Gamma] + \[Mu]) * (\[Mu] + \[Rho]))


(* ::Subsubsection::Closed:: *)
(*W**)


eeCalc4 = Expand[Weq /. {\[Xi] -> 0, Sstar -> S\[Ellipsis]corner\[Ellipsis]ee, Istar -> I\[Ellipsis]corner\[Ellipsis]ee, Jstar -> J\[Ellipsis]corner\[Ellipsis]ee}]


(* ::Text:: *)
(*This implies a quadratic equation for W**)


eeCalc5 = CoefficientList[eeCalc4, Wstar]


termAcornerCase = Simplify[eeCalc5[[3]]]


termBcornerCase = eeCalc5[[2]]


termCcornerCase = Simplify[eeCalc5[[1]]]


(* ::Subsubsection::Closed:: *)
(*Result*)


(* ::Text:: *)
(*Two equilibria has been found as W* is obtained as a solution to a quadratic equation. Epidemiological feasibility was not fully investigated, we will revisit this issue when discussing the general case.*)


(* ::Section::Closed:: *)
(*General case ( \[Xi] != 0 ): Disease Free  (DFE)*)


(* ::Text:: *)
(*We now consider the case of I* = 0 and refer to the resulting equilibrium (given that we find only one) as the disease free equilibrium)*)


I\[Ellipsis]dfe = 0;


(* ::Subsection::Closed:: *)
(*I'(t) = 0*)


Factor[Ieq]


Factor[Ieq] /. {Istar -> I\[Ellipsis]dfe}


(* ::Text:: *)
(*Clearly, we have 2 possibilities: J* = 0 or S* = 0.*)


(* ::Subsection::Closed:: *)
(*Case 1: S* = 0*)


Ieq /. {Istar -> 0, Sstar -> 0}


Seq /. {Istar -> 0, Sstar -> 0}


Solve[{Seq == 0} /. {Istar -> 0, Sstar -> 0}, {Wstar}]


(* ::Text:: *)
(*Clearly this cannot be epidemiologically feasible.  Nevertheless, let's continue to see if there is a mathematically valid equilibrium.*)


Jeq /. {Istar -> 0, Sstar -> 0, Wstar -> - \[Mu] / (\[Kappa] * \[Omega])}


Coefficient[Jeq /. {Istar -> 0, Sstar -> 0, Wstar -> - \[Mu] / (\[Kappa] * \[Omega])}, Jstar]


(* ::Text:: *)
(*As all parameters are non-negative and \[Mu] and \[Rho] are positive, this term cannot be 0. Hence, J* = 0 must hold.*)


Weq /. {Istar -> 0, Sstar -> 0, Wstar -> - \[Mu] / (\[Kappa] * \[Omega]), Jstar -> 0}


(* ::Text:: *)
(*As all parameters are non-negative and \[Alpha] and \[Kappa] are positive, this term cannot be 0. Hence, there are no solutions in this case.*)


(* ::Subsection::Closed:: *)
(*Case 2: J* = 0 *)


J\[Ellipsis]dfe = 0;


(* ::Subsubsection::Closed:: *)
(*S* and  W**)


(* ::Text:: *)
(*S'(t) = 0 and W'(t) = 0, hence, S'(t) - W'(t) = 0*)


Expand[Seq /. {Istar -> I\[Ellipsis]dfe, Jstar -> J\[Ellipsis]dfe}]


(* ::Text:: *)
(*We know that S* != 0 from above, hence, *)


W\[Ellipsis]dfe\[Ellipsis]intermediate = Wstar /. First[Solve[(Seq /. {Istar -> I\[Ellipsis]dfe, Jstar -> J\[Ellipsis]dfe}) == 0, Wstar]]


Simplify[Weq /. {Istar -> I\[Ellipsis]dfe, Jstar -> J\[Ellipsis]dfe, Wstar -> W\[Ellipsis]dfe\[Ellipsis]intermediate}]


(* ::Text:: *)
(*Hence,*)


S\[Ellipsis]dfe = 1


W\[Ellipsis]dfe = Simplify[W\[Ellipsis]dfe\[Ellipsis]intermediate /. {Sstar -> S\[Ellipsis]dfe}]


(* ::Subsection::Closed:: *)
(*Result*)


{
Sstar -> S\[Ellipsis]dfe,
Istar -> I\[Ellipsis]dfe,
Jstar -> J\[Ellipsis]dfe,
Wstar -> W\[Ellipsis]dfe
} // TableForm


(* ::Section::Closed:: *)
(*General case ( \[Xi] != 0 ): Endemic Equilibrium (EE)*)


(* ::Subsection::Closed:: *)
(*Intermediate equations for S*, I*, and J* as functions of W**)


(* ::Text:: *)
(*We express J* from I'=0 and J'=0*)


eeCalc10 = Solve[Ieq == 0, {Jstar}]


eeCalc11 = Solve[Jeq == 0, {Jstar}]


(* ::Text:: *)
(*As I* is not 0, we can simplify*)


eeCalc12 = Simplify[Last[First[First[eeCalc10]]] / Istar]


eeCalc13 = Simplify[Last[First[First[eeCalc11]]] / Istar]


eeCalc14 = Solve[eeCalc12 == eeCalc13, {Sstar}]


Simplify[Last[First[First[eeCalc14]]] - ((\[Gamma] + \[Mu]) / \[Beta] - (\[Xi] * \[Nu] * (\[Gamma] + \[Mu]) * Wstar) / (\[Rho] + \[Mu]))]


S\[Ellipsis]ee\[Ellipsis]intermediate = (\[Gamma] + \[Mu]) / \[Beta] - (\[Xi] * \[Nu] * (\[Gamma] + \[Mu]) * Wstar) / (\[Rho] + \[Mu])


(* ::Text:: *)
(*We use the formula for S* to get I* as follows*)


eeCalc15 = Solve[{Seq + Ieq == 0} /. {Sstar -> S\[Ellipsis]ee\[Ellipsis]intermediate}, {Istar}]


Simplify[Last[First[First[eeCalc15]]] - ( \[Mu] * ( 1 / (\[Gamma] + \[Mu]) - 1 / \[Beta] ) + Wstar * ( \[Mu] * \[Nu] * \[Xi] / (\[Mu] + \[Rho]) + \[Kappa] * \[Omega] / (\[Gamma] + \[Mu]) ) )]


I\[Ellipsis]ee\[Ellipsis]intermediate = \[Mu] * (1 / (\[Gamma] + \[Mu]) - 1 / \[Beta]) + Wstar * ( \[Mu] * \[Nu] * \[Xi] / (\[Mu] + \[Rho]) + \[Kappa] * \[Omega] / (\[Gamma] + \[Mu]) )


(* ::Text:: *)
(*Finally, we obtain the formula for J**)


Simplify[Solve[{Ieq == 0} /. {Sstar -> S\[Ellipsis]ee\[Ellipsis]intermediate}, {Jstar}]]


J\[Ellipsis]ee\[Ellipsis]intermediate = \[Beta] * \[Nu] / (\[Mu] + \[Rho] - \[Nu] * \[Beta] * \[Xi] * Wstar) * Wstar * Istar


(* ::Subsection::Closed:: *)
(*W**)


eeCalc21 = Simplify[(Weq /. {Jstar -> J\[Ellipsis]ee\[Ellipsis]intermediate}) /. {Sstar -> S\[Ellipsis]ee\[Ellipsis]intermediate, Istar -> I\[Ellipsis]ee\[Ellipsis]intermediate}]


eeCalc22 = Simplify[Expand[eeCalc21 * (\[Mu] - Wstar * \[Beta] * \[Nu] * \[Xi] + \[Rho]) * (\[Gamma] + \[Mu]) * (\[Mu] + \[Rho]) * \[Beta]]]


(* ::Text:: *)
(*We obtain a quadratic equation in W**)


eeCalc23 = CoefficientList[eeCalc22, Wstar];
eeCalc23 //MatrixForm


(* ::Text:: *)
(*New notations*)


\[Omega]rule = {\[Omega] -> \[Alpha] / (\[Alpha] - 1)}


\[Eta]rule = {(\[Eta] -> \[Alpha] * \[Omega]) /. \[Omega]rule}


Q0rule = {Q0 -> \[Alpha] * \[Gamma] * \[Kappa]}


Q1rule = {Q1 -> (\[Rho] + \[Mu]) * (\[Kappa]^2 * \[Eta] + (\[Gamma] + \[Mu]) * (\[Mu] + \[Kappa] * \[Eta]))}


Q2rule = {Q2 -> (\[Alpha] * \[Kappa] + (\[Mu] + \[Rho]))}


(* ::Text:: *)
(*The lead coefficient: A*)


Simplify[eeCalc23[[3]]]


TermA = \[Beta]^2 * \[Nu] * (
	\[Xi] * Q1 +
	\[Kappa] * \[Alpha] * (\[Mu] + \[Rho]) * Q2 - (\[Gamma] + \[Mu]) * \[Nu] * \[Xi]^2 * Q0 - 
	\[Nu] * \[Xi] * (\[Gamma] + \[Mu]) * \[Mu] * Q2 -
	\[Kappa] * \[Eta] * (\[Mu] + \[Rho]) * Q2
)


Simplify[((TermA - Simplify[eeCalc23[[3]]]) /. Join[Q0rule, Q1rule, Q2rule]) /. Join[\[Omega]rule, \[Eta]rule]]


(* ::Text:: *)
(*The linear term: B*)


Simplify[eeCalc23[[2]]]


TermB = \[Beta] * (\[Mu] + \[Rho]) * (
	(\[Gamma] + \[Mu]) * \[Nu] * \[Xi] * Q0 -  
	(\[Beta] - (\[Gamma] + \[Mu])) * \[Nu] * \[Mu] * Q2 - 
	Q1 - (\[Beta] - (\[Gamma] + \[Mu])) * \[Nu] * \[Xi] * Q0
)


Simplify[((TermB - Simplify[eeCalc23[[2]]]) /. Join[Q0rule, Q1rule, Q2rule]) /. Join[\[Omega]rule, \[Eta]rule]]


(* ::Text:: *)
(*The constant term: C*)


Simplify[eeCalc23[[1]]]


TermC = (\[Beta] - (\[Gamma] + \[Mu])) * (\[Rho] + \[Mu])^2 * Q0


Simplify[(TermC - Simplify[eeCalc23[[1]]]) /. Join[Q0rule, Q1rule, Q2rule]]


(* ::Text:: *)
(*The quadratic equation then is*)


QuadraticW[W_] := TermA * W^2 + TermB * W + TermC


(* ::Text:: *)
(*with the discriminant*)


\[CapitalDelta] = TermB^2 - 4 * TermA * TermC


(* ::Text:: *)
(*The roots of the quadratic equation*)


W\[Ellipsis]ee\[Ellipsis]plus = Simplify[(- TermB + Sqrt[\[CapitalDelta]]) / (2 * TermA)]


W\[Ellipsis]ee\[Ellipsis]minus = Simplify[(- TermB - Sqrt[\[CapitalDelta]]) / (2 * TermA)]


(* ::Section::Closed:: *)
(*Non-negativity (epidemiological feasibility) of the EE*)


(* ::Subsection::Closed:: *)
(*WbarUP and WbarDOWN*)


(* ::Text:: *)
(*The formula for S* is decreasing in W**)


D[S\[Ellipsis]ee\[Ellipsis]intermediate, Wstar]


(* ::Text:: *)
(*Hence, W* < WbarUP must hold*)


WbarUP = Wstar /. First[Solve[S\[Ellipsis]ee\[Ellipsis]intermediate == 0, Wstar]]


(* ::Text:: *)
(*The formula for I* is increasing in W**)


D[I\[Ellipsis]ee\[Ellipsis]intermediate, Wstar]


(* ::Text:: *)
(*Hence, W* > max{0, WbarDOWN} must hold*)


WbarDOWN = Wstar /. First[Solve[I\[Ellipsis]ee\[Ellipsis]intermediate == 0, Wstar]]


(* ::Subsection::Closed:: *)
(*The quadratic formula at WbarUP and WbarDOWN*)


(* ::Text:: *)
(*As Q2 is positive we get that the quadratic formula is negative at WbarUP*)


Simplify[(QuadraticW[WbarUP] /. Join[Q0rule, Q1rule]) /. Join[\[Omega]rule]]


(* ::Text:: *)
(*As the following expression is negative for R0 < 1*)


(\[Beta] - \[Gamma] - \[Mu]) * (\[Rho] + \[Mu])^2 * (\[Omega] * \[Kappa] * (\[Rho] + \[Mu]) * Q0 + \[Mu] * Q1) * (\[Mu] * \[Nu] * \[Beta] * \[Xi] + \[Omega] * \[Kappa] * (\[Rho] + \[Mu])) / (\[Mu] * \[Nu] * \[Xi] * (\[Gamma] + \[Mu]) + \[Omega] * \[Kappa] * (\[Rho] + \[Mu]))^2


(* ::Text:: *)
(*we get that the quadratic formula is negative at WbarDOWN for R0 < 1*)


FullSimplify[((
QuadraticW[WbarDOWN] - 
(\[Beta] - \[Gamma] - \[Mu]) * (\[Rho] + \[Mu])^2 * (\[Omega] * \[Kappa] * (\[Rho] + \[Mu]) * Q0 + \[Mu] * Q1) * (\[Mu] * \[Nu] * \[Beta] * \[Xi] + \[Omega] * \[Kappa] * (\[Rho] + \[Mu])) / (\[Mu] * \[Nu] * \[Xi] * (\[Gamma] + \[Mu]) + \[Omega] * \[Kappa] * (\[Rho] + \[Mu]))^2
) /. Join[Q0rule, Q1rule, Q2rule]) /. Join[\[Omega]rule, \[Eta]rule]]


(* ::Subsection::Closed:: *)
(*The discriminant as a function of the transmission rate*)


\[CapitalDelta]


(* ::Text:: *)
(*The following transformation of the discriminant yields a quadratic function of the transmission rate*)


Simplify[\[CapitalDelta] / (\[Rho] + \[Mu])^2 / \[Beta]^2]


FullSimplify[CoefficientList[Simplify[\[CapitalDelta] / (\[Rho] + \[Mu])^2 / \[Beta]^2], \[Beta]] // MatrixForm]


(* ::Subsection::Closed:: *)
(*The condition \[CapitalTheta]*)


(* ::Text:: *)
(*The discriminant at R0 = 1 is*)


\[CapitalDelta] /. \[Beta] -> \[Gamma] + \[Mu]


(* ::Text:: *)
(*The middle term is the square of*)


\[CapitalTheta] = \[Nu] * \[Xi] * (\[Gamma] + \[Mu]) * Q0 - Q1


(* ::Subsection::Closed:: *)
(*The slope of the quadratic formula for W* at 0*)


TermB 


(* ::Text:: *)
(*that is*)


FullSimplify[(
TermB - 
\[Beta] * (\[Rho] + \[Mu]) * (\[CapitalTheta] - (\[Beta] - \[Gamma] - \[Mu]) * \[Nu] * (\[Xi] * Q0 + \[Mu] * Q2)))
]


(* ::Section::Closed:: *)
(*Transcritical bifurcation*)


(* ::Subsection::Closed:: *)
(*The Jacobian at the DFE*)


eqs = {Seq, Ieq, Weq, Jeq};
dfes = {Sstar, Istar, Wstar, Jstar};


Jacobian\[Ellipsis]dfe = Table[
	D[eqs[[i]], dfes[[j]]], {i, 1, 4}, {j, 1, 4}
] /. {Sstar -> S\[Ellipsis]dfe, Istar -> I\[Ellipsis]dfe, Wstar -> W\[Ellipsis]dfe,Jstar -> J\[Ellipsis]dfe};
Simplify[Jacobian\[Ellipsis]dfe] // TableForm


Eigenvalues[Jacobian\[Ellipsis]dfe]


(* ::Subsection::Closed:: *)
(*Eigenvectors and computation*)


transformedEqs = {Seq, Ieq, Weq, Jeq} /. {\[Beta] -> (b + \[Beta]star), Sstar -> (xS + 1), Istar -> xI, Wstar -> xW, Jstar -> xJ};
vars = {xS, xI, xW, xJ};
transformedEqs //TableForm


matrixM = Table[
	D[transformedEqs[[i]], vars[[j]]], {i, 1, 4}, {j, 1, 4}
] /. {\[Beta]star -> (\[Gamma] + \[Mu]), b -> 0, xS -> 0, xI -> 0, xW -> 0, xJ-> 0};
Simplify[matrixM] // TableForm


Eigenvalues[matrixM]


bifCalc = FullSimplify[
	First[Solve[matrixM . {w1, 1, w3, w4} == {0, 0, 0, 0}, {w1, w3, w4}]]
]


(* ::Text:: *)
(*The numerator of w1 can be shown to be - Q1 after expanding the fraction*)


FullSimplify[(((w1 /. bifCalc) + Q1 / ((\[Alpha]*\[Kappa] + \[Mu]) * (\[Kappa] * \[Omega] + \[Mu]) * (\[Rho] + \[Mu]))) /. Q1rule) /. Join[\[Omega]rule, \[Eta]rule]]


bifCalc2 = Simplify[
	First[Solve[Transpose[{v1, 1, v3, v4}] . matrixM == {0, 0, 0, 0}, {v1, v3, v4}]]
]


(* ::Section::Closed:: *)
(*Comparison of the general case to the case \[Xi] = 0*)


(* ::Text:: *)
(*We have established all formulae, the existence of a unique endemic equilibrium in the endemic scenario. Trivially, *)
(*all results can be carried over to the case \[Xi] = 0 as *)


(* ::Subsection::Closed:: *)
(*Intermediate formulae for S*, I*, and J**)


(S\[Ellipsis]corner\[Ellipsis]ee - S\[Ellipsis]ee\[Ellipsis]intermediate) /. \[Xi] -> 0


FullSimplify[(I\[Ellipsis]corner\[Ellipsis]ee - I\[Ellipsis]ee\[Ellipsis]intermediate) /. \[Xi] -> 0]


FullSimplify[(J\[Ellipsis]corner\[Ellipsis]ee - J\[Ellipsis]ee\[Ellipsis]intermediate /. Istar -> I\[Ellipsis]ee\[Ellipsis]intermediate) /. \[Xi] -> 0]


(* ::Subsection::Closed:: *)
(*The quadratic equation for W**)


FullSimplify[((
(TermA /. \[Xi] -> 0) - 
termAcornerCase * (\[Gamma] + \[Mu]) * (\[Rho] + \[Mu])^2 * \[Beta]
) /. Join[Q0rule, Q1rule, Q2rule]) /. Join[\[Omega]rule, \[Eta]rule]
]


FullSimplify[((
(TermB /. \[Xi] -> 0) - 
termBcornerCase * (\[Gamma] + \[Mu]) * (\[Rho] + \[Mu])^2 * \[Beta]
) /. Join[Q0rule, Q1rule, Q2rule]) /. Join[\[Omega]rule, \[Eta]rule]
]


FullSimplify[((
(TermC /. \[Xi] -> 0) - 
termCcornerCase * (\[Gamma] + \[Mu]) * (\[Rho] + \[Mu])^2 * \[Beta]
) /. Join[Q0rule, Q1rule, Q2rule]) /. Join[\[Omega]rule, \[Eta]rule]
]


(* ::Text:: *)
(*So the quadratic equations for W* are scaled versions of each other (positive scaling factor) *)
(*and the formulae for the other equilibria coincide. *)
(*Consequently, a unique endemic equilibrium exists in the case \[Xi] = 0 as well when \[Beta]  >= \[Gamma] + \[Mu]. *)


(* ::Text:: *)
(*Moreover, the lead coefficient is negative so we have a downward parabola*)


termAcornerCase


(* ::Subsection::Closed:: *)
(*WbarUP becomes \[Infinity]*)


WbarUP


(* ::Subsection::Closed:: *)
(*\[CapitalTheta] < 0*)


\[CapitalTheta] /. \[Xi] -> 0


(* ::Chapter:: *)
(*The Routh-Hurwitz Criterion*)


(* ::Section::Closed:: *)
(*The characteristic polynomial*)


(* ::Subsection::Closed:: *)
(*Jacobian*)


eqs = {Seq, Ieq, Weq, Jeq};
ees = {Sstar, Istar, Wstar, Jstar};


Table[
	D[eqs[[i]], ees[[j]]], {i, 1, 4}, {j, 1, 4}
]//TableForm


Jacobian\[Ellipsis]ee = Table[
	D[eqs[[i]], ees[[j]]], {i, 1, 4}, {j, 1, 4}
] /. {Sstar -> S\[Ellipsis]ee\[Ellipsis]intermediate};
Simplify[Jacobian\[Ellipsis]ee] // TableForm


FullSimplify[Istar + \[Xi] * J\[Ellipsis]ee\[Ellipsis]intermediate]


Jacobian\[Ellipsis]ee = Jacobian\[Ellipsis]ee /. {(Istar + \[Xi] * Jstar) -> FullSimplify[Istar + \[Xi] * J\[Ellipsis]ee\[Ellipsis]intermediate]};
Simplify[Jacobian\[Ellipsis]ee] // TableForm


(* ::Subsection::Closed:: *)
(*Characteristic polynomial*)


{a4\[Ellipsis]1,a3\[Ellipsis]1, a2\[Ellipsis]1, a1\[Ellipsis]1, a0} = 
CoefficientList[
	Det[
		DiagonalMatrix[{\[Lambda], \[Lambda], \[Lambda], \[Lambda]}] - Jacobian\[Ellipsis]ee
	], 
\[Lambda]];


a0


a1\[Ellipsis]1


a2\[Ellipsis]1


a3\[Ellipsis]1


a4\[Ellipsis]1


(* ::Section:: *)
(*Positivity of the coefficients a_i*)


(* ::Subsubsection::Closed:: *)
(*Service code*)


WeightedElement[list_, idx_, w_] := (w * list[[idx]])


SelectElementsWithID[list_, ids_] := Map[
	list[[#]] &,
	ids
]


(* ::Subsection::Closed:: *)
(*a0*)


a0


(* ::Subsection::Closed:: *)
(*a1*)


FullSimplify[a1\[Ellipsis]1]


a1 = \[Eta] * \[Kappa] + 2 * \[Mu] + (\[Gamma] + \[Mu]) / (\[Rho] + \[Mu]) * Wstar * \[Beta] * \[Nu] * \[Xi] + (\[Rho] + \[Mu] - Wstar * \[Beta] * \[Nu] * \[Xi]) + Istar * \[Beta] * (1 + \[Nu]) * (\[Rho] + \[Mu]) / (\[Rho] + \[Mu] - Wstar * \[Beta] * \[Nu] * \[Xi])


FullSimplify[(a1 - a1\[Ellipsis]1) /. Join[\[Omega]rule, \[Eta]rule]]


(* ::Text:: *)
(*As \[Mu] + \[Rho] >= W* \[Beta] \[Nu] \[Xi], this term is positive*)


(* ::Subsection::Closed:: *)
(*a2*)


(* ::Subsubsection::Closed:: *)
(*Computation*)


Expand[a2\[Ellipsis]1]


eeCalc24 = GroupBy[List @@ Expand[a2\[Ellipsis]1], Internal`SyntacticNegativeQ]


a2\[Ellipsis]eliminations = {}


{Length[eeCalc24[True]], Length[eeCalc24[False]]}


Simplify[1/3 * eeCalc24[False][[6]] + eeCalc24[False][[9]] + eeCalc24[True][[1]]]


a2\[Ellipsis]eliminations = Join[a2\[Ellipsis]eliminations, {{{{6, 1/3}, {9, 1}}, {{1, 1}}}}];


Simplify[eeCalc24[False][[3]] + eeCalc24[False][[7]] + eeCalc24[True][[2]]]


a2\[Ellipsis]eliminations = Join[a2\[Ellipsis]eliminations, {{{{3, 1}, {7, 1}}, {{2, 1}}}}];


Simplify[eeCalc24[False][[4]] + eeCalc24[False][[10]] + eeCalc24[False][[8]] + eeCalc24[True][[3]]]


a2\[Ellipsis]eliminations = Join[a2\[Ellipsis]eliminations, {{{{4, 1}, {10, 1}, {8, 1}}, {{3, 1}}}}];


Simplify[1/4 * eeCalc24[False][[21]] + 1/3 * eeCalc24[False][[16]] + eeCalc24[True][[4]]]


a2\[Ellipsis]eliminations = Join[a2\[Ellipsis]eliminations, {{{{21, 1/4}, {16, 1/3}}, {{4, 1}}}}];


Simplify[1/4 * eeCalc24[False][[21]] + eeCalc24[False][[24]] + eeCalc24[True][[5]]]


a2\[Ellipsis]eliminations = Join[a2\[Ellipsis]eliminations, {{{{21, 1/4}, {24, 1}}, {{5, 1}}}}];


Simplify[eeCalc24[False][[32]] + eeCalc24[False][[34]] + eeCalc24[True][[6]]]


a2\[Ellipsis]eliminations = Join[a2\[Ellipsis]eliminations, {{{{32, 1}, {34, 1}}, {{6, 1}}}}];


(* ::Subsubsection::Closed:: *)
(*Proof of positivity*)


a2\[Ellipsis]eliminations


a2\[Ellipsis]residual = Map[
	Function[elimination, 
		Simplify[Total[Join[
		Map[
			WeightedElement[eeCalc24[False], #[[1]], #[[2]]] &
			,elimination[[1]]
		],
		Map[
			WeightedElement[eeCalc24[True], #[[1]], #[[2]]] &
			,elimination[[2]]
		]
		]]]
	]
	,a2\[Ellipsis]eliminations
]


(* ::Text:: *)
(*Hence, the residual is*)


FullSimplify[Total[a2\[Ellipsis]residual]]


(* ::Text:: *)
(*Check to what extent are the components of a2 used / eliminated:*)


a2\[Ellipsis]positiveWeights = ConstantArray[0, Length[eeCalc24[False]]];
Map[
	Function[elimination, 
		Map[
			(a2\[Ellipsis]positiveWeights[[#[[1]]]] = a2\[Ellipsis]positiveWeights[[#[[1]]]] + #[[2]]) &
			,elimination[[1]]
		]
	]
	,a2\[Ellipsis]eliminations
];
a2\[Ellipsis]positiveWeights


(* ::Text:: *)
(*Check that all syntactically negative components have been eliminated*)


a2\[Ellipsis]negativeWeights = ConstantArray[0, Length[eeCalc24[True]]];
Map[
	Function[elimination, 
		Map[
			(a2\[Ellipsis]negativeWeights[[#[[1]]]] = a2\[Ellipsis]negativeWeights[[#[[1]]]] + #[[2]]) &
			,elimination[[2]]
		]
	]
	,a2\[Ellipsis]eliminations
];
a2\[Ellipsis]negativeWeights


(* ::Text:: *)
(*The weights describing the unused syntactically positive components*)


a2\[Ellipsis]remainingPositiveWeights = 1 - a2\[Ellipsis]positiveWeights


(* ::Text:: *)
(*Hence, a2 is the sum of the positive residual and some positive terms*)


a2\[Ellipsis]2 = Total[a2\[Ellipsis]residual] + a2\[Ellipsis]remainingPositiveWeights . eeCalc24[False]


(* ::Text:: *)
(*Check*)


FullSimplify[a2\[Ellipsis]2 - a2\[Ellipsis]1]


(* ::Subsubsection::Closed:: *)
(*Further simplifications*)


a2 = 0;


a2\[Ellipsis]residual


FullSimplify @ Total @ SelectElementsWithID[a2\[Ellipsis]residual, {4, 5}]


a2 = a2 + FullSimplify @ Total @ SelectElementsWithID[a2\[Ellipsis]residual, {4, 5}];


FullSimplify @ Total @ SelectElementsWithID[a2\[Ellipsis]residual, {2, 3, 6}]


FullSimplify @ Total @ SelectElementsWithID[a2\[Ellipsis]residual, {2, 3, 6}] /. (\[Alpha] + \[Omega]) -> \[Eta]


a2 = a2 + FullSimplify @ Total @ SelectElementsWithID[a2\[Ellipsis]residual, {2, 3, 6}] /. (\[Alpha] + \[Omega]) -> \[Eta];


eeCalc100 = List @@ (a2\[Ellipsis]remainingPositiveWeights . eeCalc24[False])


Length[eeCalc100]


SelectElementsWithID[eeCalc100, {1, 2, 23, 24}]


a2 = a2 + 2 * \[Eta] * \[Kappa] * \[Mu] + 3 * \[Mu]^2 + \[Eta] * \[Kappa]^2; 


FullSimplify @ Total @ SelectElementsWithID[eeCalc100, {5, 6, 7}]


a2 = a2 + FullSimplify @ Total @ SelectElementsWithID[eeCalc100, {5, 6, 7}];


FullSimplify @ Total @ SelectElementsWithID[eeCalc100, {8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 26, 27}]


FullSimplify @ (Total @ SelectElementsWithID[eeCalc100, {8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 26, 27}] /. \[Omega] -> \[Eta] - \[Alpha])


a2 = a2 + FullSimplify @ (Total @ SelectElementsWithID[eeCalc100, {8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 26, 27}] /. \[Omega] -> \[Eta] - \[Alpha]);


FullSimplify @ Total @ SelectElementsWithID[eeCalc100, {19, 20, 21, 22}]


a2 = a2 + FullSimplify @ Total @ SelectElementsWithID[eeCalc100, {19, 20, 21, 22}];


FullSimplify @ Total @ SelectElementsWithID[eeCalc100, {3, 4, 25}]


FullSimplify @ Total @ SelectElementsWithID[eeCalc100, {3, 4, 25}] /. (\[Alpha] + \[Omega]) -> \[Eta]


a2 = a2 + (FullSimplify @ Total @ SelectElementsWithID[eeCalc100, {3, 4, 25}] /. (\[Alpha] + \[Omega]) -> \[Eta]);


a2


(* ::Text:: *)
(*Check*)


FullSimplify[(a2 - a2\[Ellipsis]1) /. Join[\[Omega]rule, \[Eta]rule]]


(* ::Subsection::Closed:: *)
(*a3*)


(* ::Subsubsection::Closed:: *)
(*Computation*)


Expand[a3\[Ellipsis]1]


eeCalc25 = GroupBy[List @@ Expand[a3\[Ellipsis]1], Internal`SyntacticNegativeQ]


MapIndexed[
	{#1, #2[[1]]} &,
	eeCalc25[False]
]


MapIndexed[
	{#1, #2[[1]]} &,
	eeCalc25[True]
]


a3\[Ellipsis]eliminations = {}


{Length[eeCalc25[True]], Length[eeCalc25[False]]}


Simplify[1/2 * eeCalc25[False][[5]] + eeCalc25[False][[9]] + eeCalc25[True][[1]]]


a3\[Ellipsis]eliminations = Join[a3\[Ellipsis]eliminations, {{{{5, 1/2}, {9, 1}}, {{1, 1}}}}];


Simplify[2/3 * eeCalc25[False][[6]] + eeCalc25[False][[10]] + eeCalc25[True][[2]]]


a3\[Ellipsis]eliminations = Join[a3\[Ellipsis]eliminations, {{{{6, 2/3}, {10, 1}}, {{2, 1}}}}];


Simplify[eeCalc25[False][[3]] + eeCalc25[False][[7]] + eeCalc25[False][[11]] + eeCalc25[True][[3]]]


a3\[Ellipsis]eliminations = Join[a3\[Ellipsis]eliminations, {{{{3, 1}, {7, 1}, {11, 1}}, {{3, 1}}}}];


Simplify[eeCalc25[False][[4]] + eeCalc25[False][[8]] + eeCalc25[False][[12]] + eeCalc25[True][[4]]]


a3\[Ellipsis]eliminations = Join[a3\[Ellipsis]eliminations, {{{{4, 1}, {8, 1}, {12, 1}}, {{4, 1}}}}];


Simplify[1/2 * eeCalc25[False][[52]] + eeCalc25[False][[55]] + eeCalc25[True][[11]]]


a3\[Ellipsis]eliminations = Join[a3\[Ellipsis]eliminations, {{{{52, 1/2}, {55, 1}}, {{11, 1}}}}];


Simplify[eeCalc25[False][[49]] + eeCalc25[False][[53]] + eeCalc25[True][[12]]]


a3\[Ellipsis]eliminations = Join[a3\[Ellipsis]eliminations, {{{{49, 1}, {53, 1}}, {{12, 1}}}}];


Simplify[eeCalc25[False][[50]] + eeCalc25[False][[54]] + eeCalc25[False][[56]] + eeCalc25[True][[13]]]


a3\[Ellipsis]eliminations = Join[a3\[Ellipsis]eliminations, {{{{50, 1}, {54, 1}, {56, 1}}, {{13, 1}}}}];


Simplify[1/3 * eeCalc25[False][[32]] + 1/2 * eeCalc25[False][[24]] + eeCalc25[True][[5]]]


a3\[Ellipsis]eliminations = Join[a3\[Ellipsis]eliminations, {{{{32, 1/3}, {24, 1/2}}, {{5, 1}}}}];


Simplify[1/3 * eeCalc25[False][[33]] + 1/2 * eeCalc25[False][[25]] + eeCalc25[True][[6]]]


a3\[Ellipsis]eliminations = Join[a3\[Ellipsis]eliminations, {{{{33, 1/3}, {25, 1/2}}, {{6, 1}}}}];


Simplify[2/3 * eeCalc25[False][[26]] + 2/5 * eeCalc25[False][[34]] + eeCalc25[True][[7]]]


a3\[Ellipsis]eliminations = Join[a3\[Ellipsis]eliminations, {{{{26, 2/3}, {34, 2/5}}, {{7, 1}}}}];


Simplify[1/3 * eeCalc25[False][[32]] + eeCalc25[False][[37]] + eeCalc25[True][[8]]]


a3\[Ellipsis]eliminations = Join[a3\[Ellipsis]eliminations, {{{{32, 1/3}, {37, 1}}, {{8, 1}}}}];


Simplify[1/3 * eeCalc25[False][[33]] + eeCalc25[False][[38]] + eeCalc25[True][[9]]]


a3\[Ellipsis]eliminations = Join[a3\[Ellipsis]eliminations, {{{{33, 1/3}, {38, 1}}, {{9, 1}}}}];


Simplify[eeCalc25[False][[39]] + 2/5 * eeCalc25[False][[34]] + eeCalc25[True][[10]]]


a3\[Ellipsis]eliminations = Join[a3\[Ellipsis]eliminations, {{{{39, 1}, {34, 2/5}}, {{10, 1}}}}];


Simplify[1/2 * eeCalc25[False][[59]] + 1/3 * eeCalc25[False][[63]] + eeCalc25[True][[14]]]


a3\[Ellipsis]eliminations = Join[a3\[Ellipsis]eliminations, {{{{59, 1/2}, {63, 1/3}}, {{14, 1}}}}];


Simplify[eeCalc25[False][[65]] + 1/3 * eeCalc25[False][[63]] + eeCalc25[True][[15]]]


a3\[Ellipsis]eliminations = Join[a3\[Ellipsis]eliminations, {{{{65, 1}, {63, 1/3}}, {{15, 1}}}}];


(* ::Subsubsection::Closed:: *)
(*Proof of positivity*)


a3\[Ellipsis]eliminations


a3\[Ellipsis]residual = Map[
	Function[elimination, 
		Simplify[Total[Join[
		Map[
			WeightedElement[eeCalc25[False], #[[1]], #[[2]]] &
			,elimination[[1]]
		],
		Map[
			WeightedElement[eeCalc25[True], #[[1]], #[[2]]] &
			,elimination[[2]]
		]
		]]]
	]
	,a3\[Ellipsis]eliminations
]


(* ::Text:: *)
(*Hence, the residual is*)


FullSimplify[Total[a3\[Ellipsis]residual]]


(* ::Text:: *)
(*Check to what extent are the components of a3 used / eliminated:*)


a3\[Ellipsis]positiveWeights = ConstantArray[0, Length[eeCalc25[False]]];
Map[
	Function[elimination, 
		Map[
			(a3\[Ellipsis]positiveWeights[[#[[1]]]] = a3\[Ellipsis]positiveWeights[[#[[1]]]] + #[[2]]) &
			,elimination[[1]]
		]
	]
	,a3\[Ellipsis]eliminations
];
a3\[Ellipsis]positiveWeights


(* ::Text:: *)
(*Check that all syntactically negative components have been eliminated*)


a3\[Ellipsis]negativeWeights = ConstantArray[0, Length[eeCalc25[True]]];
Map[
	Function[elimination, 
		Map[
			(a3\[Ellipsis]negativeWeights[[#[[1]]]] = a3\[Ellipsis]negativeWeights[[#[[1]]]] + #[[2]]) &
			,elimination[[2]]
		]
	]
	,a3\[Ellipsis]eliminations
];
a3\[Ellipsis]negativeWeights


(* ::Text:: *)
(*The weights describing the unused syntactically positive components*)


a3\[Ellipsis]remainingPositiveWeights = 1 - a3\[Ellipsis]positiveWeights


(* ::Text:: *)
(*Hence, a3 is the sum of the positive residual and some positive terms*)


a3\[Ellipsis]2 = Total[a3\[Ellipsis]residual] + a3\[Ellipsis]remainingPositiveWeights . eeCalc25[False]


(* ::Text:: *)
(*Check*)


FullSimplify[a3\[Ellipsis]2 - a3\[Ellipsis]1]


(* ::Subsubsection::Closed:: *)
(*Further simplifications*)


a3 = 0;


a3\[Ellipsis]residual


FullSimplify @ Total @ SelectElementsWithID[a3\[Ellipsis]residual, {3, 4, 6, 7}]


a3 = a3 + FullSimplify @ Total @ SelectElementsWithID[a3\[Ellipsis]residual, {3, 4, 6, 7}];


FullSimplify @ Total @ SelectElementsWithID[a3\[Ellipsis]residual, {8, 9, 10, 11, 12, 13, 14, 15}]


a3 = a3 + FullSimplify @ Total @ SelectElementsWithID[a3\[Ellipsis]residual, {8, 9, 10, 11, 12, 13, 14, 15}];


eeCalc110 = List @@ (a3\[Ellipsis]remainingPositiveWeights . eeCalc25[False])


Length[eeCalc110]


Select[eeCalc110, Denominator[#] == 1 &]


a3 = a3 + \[Eta] * \[Kappa] * \[Mu]^2 + \[Mu]^3 + \[Eta] * \[Mu] * \[Kappa]^2;


FullSimplify @ Total @ Select[eeCalc110, Denominator[#] == \[Mu] + \[Rho] &]


a3 = a3 + FullSimplify @ Total @ Select[eeCalc110, Denominator[#] == \[Mu] + \[Rho] &];


FullSimplify @ Total @ Select[eeCalc110, And[Denominator[#] == \[Mu] - Wstar * \[Beta] * \[Nu] * \[Xi] + \[Rho], FreeQ[Numerator[#], Wstar]] &]


a3 = a3 + FullSimplify @ Total @ Select[eeCalc110, And[Denominator[#] == \[Mu] - Wstar * \[Beta] * \[Nu] * \[Xi] + \[Rho], FreeQ[Numerator[#], Wstar]] &];


FullSimplify @ Total @ Select[eeCalc110, And[Denominator[#] == \[Mu] - Wstar * \[Beta] * \[Nu] * \[Xi] + \[Rho], Not[FreeQ[Numerator[#], Wstar]]] &]


a3 = a3 + FullSimplify @ Total @ Select[eeCalc110, And[Denominator[#] == \[Mu] - Wstar * \[Beta] * \[Nu] * \[Xi] + \[Rho], Not[FreeQ[Numerator[#], Wstar]]] &];


FullSimplify @ Total @ Select[eeCalc110, Denominator[#] == (\[Mu] - Wstar * \[Beta] * \[Nu] * \[Xi] + \[Rho])^2 &]


a3 = a3 + FullSimplify @ Total @ Select[eeCalc110, Denominator[#] == (\[Mu] - Wstar * \[Beta] * \[Nu] * \[Xi] + \[Rho])^2 &];


FullSimplify @ Total @ Select[eeCalc110, Denominator[#] == (\[Mu] + \[Rho])*(\[Mu] - Wstar * \[Beta] * \[Nu] * \[Xi] + \[Rho]) &]


a3 = a3 + FullSimplify @ Total @ Select[eeCalc110, Denominator[#] == (\[Mu] + \[Rho])*(\[Mu] - Wstar * \[Beta] * \[Nu] * \[Xi] + \[Rho]) &];


(* ::Text:: *)
(*Check*)


FullSimplify[(a3 - a3\[Ellipsis]1) /. Join[\[Omega]rule, \[Eta]rule]]


(* ::Subsection::Closed:: *)
(*a4 (residual)*)


(* ::Subsubsection::Closed:: *)
(*Computation*)


eeCalc26 = GroupBy[List @@ Expand[a4\[Ellipsis]1], Internal`SyntacticNegativeQ];


eeCalc27 = MapIndexed[
	{#1, #2[[1]]} &,
	eeCalc26[False]
]


eeCalc28 = MapIndexed[
	{#1, #2[[1]]} &,
	eeCalc26[True]
]


a4\[Ellipsis]eliminations = {}


{Length[eeCalc26[True]], Length[eeCalc26[False]]}


Simplify[eeCalc26[False][[1]] + eeCalc26[False][[5]] + eeCalc26[True][[1]]]


a4\[Ellipsis]eliminations = Join[a4\[Ellipsis]eliminations, {{{{1, 1}, {5, 1}}, {{1, 1}}}}];


Simplify[eeCalc26[False][[2]] + eeCalc26[False][[6]] + eeCalc26[True][[2]]]


a4\[Ellipsis]eliminations = Join[a4\[Ellipsis]eliminations, {{{{2, 1}, {6, 1}}, {{2, 1}}}}];


Simplify[eeCalc26[False][[3]] + eeCalc26[False][[7]] + eeCalc26[True][[3]]]


a4\[Ellipsis]eliminations = Join[a4\[Ellipsis]eliminations, {{{{3, 1}, {7, 1}}, {{3, 1}}}}];


Simplify[eeCalc26[False][[4]] + eeCalc26[False][[8]] + eeCalc26[True][[4]]]


a4\[Ellipsis]eliminations = Join[a4\[Ellipsis]eliminations, {{{{4, 1}, {8, 1}}, {{4, 1}}}}];


Simplify[eeCalc26[False][[45]] + eeCalc26[False][[49]] + eeCalc26[True][[17]]]


a4\[Ellipsis]eliminations = Join[a4\[Ellipsis]eliminations, {{{{45, 1}, {49, 1}}, {{17, 1}}}}];


Simplify[eeCalc26[False][[46]] + eeCalc26[False][[50]] + eeCalc26[True][[18]]]


a4\[Ellipsis]eliminations = Join[a4\[Ellipsis]eliminations, {{{{46, 1}, {50, 1}}, {{18, 1}}}}];


Simplify[eeCalc26[False][[47]] + eeCalc26[False][[51]] + eeCalc26[True][[19]]]


a4\[Ellipsis]eliminations = Join[a4\[Ellipsis]eliminations, {{{{47, 1}, {51, 1}}, {{19, 1}}}}];


Simplify[eeCalc26[False][[48]] + eeCalc26[False][[52]] + eeCalc26[True][[20]]]


a4\[Ellipsis]eliminations = Join[a4\[Ellipsis]eliminations, {{{{48, 1}, {52, 1}}, {{20, 1}}}}];


Simplify[eeCalc26[False][[23]] + 1/2 * eeCalc26[False][[31]] + eeCalc26[True][[5]]]


a4\[Ellipsis]eliminations = Join[a4\[Ellipsis]eliminations, {{{{23, 1}, {31, 1/2}}, {{5, 1}}}}];


Simplify[eeCalc26[False][[24]] + 1/2 * eeCalc26[False][[32]] + eeCalc26[True][[7]]]


a4\[Ellipsis]eliminations = Join[a4\[Ellipsis]eliminations, {{{{24, 1}, {32, 1/2}}, {{7, 1}}}}];


Simplify[eeCalc26[False][[25]] + 1/2 * eeCalc26[False][[33]] + eeCalc26[True][[8]]]


a4\[Ellipsis]eliminations = Join[a4\[Ellipsis]eliminations, {{{{25, 1}, {33, 1/2}}, {{8, 1}}}}];


Simplify[eeCalc26[False][[35]] + 1/2 * eeCalc26[False][[31]] + eeCalc26[True][[11]]]


a4\[Ellipsis]eliminations = Join[a4\[Ellipsis]eliminations, {{{{35, 1}, {31, 1/2}}, {{11, 1}}}}];


Simplify[eeCalc26[False][[36]] + 1/2 * eeCalc26[False][[32]] + eeCalc26[True][[13]]]


a4\[Ellipsis]eliminations = Join[a4\[Ellipsis]eliminations, {{{{36, 1}, {32, 1/2}}, {{13, 1}}}}];


Simplify[eeCalc26[False][[37]] + 1/2 * eeCalc26[False][[33]] + eeCalc26[True][[14]]]


a4\[Ellipsis]eliminations = Join[a4\[Ellipsis]eliminations, {{{{37, 1}, {33, 1/2}}, {{14, 1}}}}];


Simplify[eeCalc26[False][[38]] + 1/2 * eeCalc26[False][[34]] + eeCalc26[True][[16]]]


a4\[Ellipsis]eliminations = Join[a4\[Ellipsis]eliminations, {{{{38, 1}, {34, 1/2}}, {{16, 1}}}}];


Simplify[eeCalc26[False][[53]] + 1/2 * eeCalc26[False][[58]] + eeCalc26[True][[21]]]


a4\[Ellipsis]eliminations = Join[a4\[Ellipsis]eliminations, {{{{53, 1}, {58, 1/2}}, {{21, 1}}}}];


Simplify[eeCalc26[False][[54]] + 1/2 * eeCalc26[False][[59]] + eeCalc26[True][[22]]]


a4\[Ellipsis]eliminations = Join[a4\[Ellipsis]eliminations, {{{{54, 1}, {59, 1/2}}, {{22, 1}}}}];


Simplify[eeCalc26[False][[55]] + 1/2 * eeCalc26[False][[60]] + eeCalc26[True][[23]]]


a4\[Ellipsis]eliminations = Join[a4\[Ellipsis]eliminations, {{{{55, 1}, {60, 1/2}}, {{23, 1}}}}];


Simplify[eeCalc26[False][[63]] + 1/2 * eeCalc26[False][[58]] + eeCalc26[True][[24]]]


a4\[Ellipsis]eliminations = Join[a4\[Ellipsis]eliminations, {{{{63, 1}, {58, 1/2}}, {{24, 1}}}}];


Simplify[eeCalc26[False][[64]] + 1/2 * eeCalc26[False][[59]] + eeCalc26[True][[25]]]


a4\[Ellipsis]eliminations = Join[a4\[Ellipsis]eliminations, {{{{64, 1}, {59, 1/2}}, {{25, 1}}}}];


Simplify[eeCalc26[False][[65]] + 1/2 * eeCalc26[False][[60]] + eeCalc26[True][[26]]]


a4\[Ellipsis]eliminations = Join[a4\[Ellipsis]eliminations, {{{{65, 1}, {60, 1/2}}, {{26, 1}}}}];


Simplify[eeCalc26[False][[26]] + 1/2 * eeCalc26[False][[34]] + eeCalc26[True][[10]]]


a4\[Ellipsis]eliminations = Join[a4\[Ellipsis]eliminations, {{{{26, 1}, {34, 1/2}}, {{10, 1}}}}];


Expand[FullSimplify[eeCalc26[False][[30]] + eeCalc26[True][[9]] + eeCalc26[True][[15]]]]


a4\[Ellipsis]eliminations = Join[a4\[Ellipsis]eliminations, {{{{30, 1}}, {{9, 1}, {15, 1}}}}];


Expand[FullSimplify[eeCalc26[False][[29]] + eeCalc26[True][[6]] + eeCalc26[True][[12]]]]


a4\[Ellipsis]eliminations = Join[a4\[Ellipsis]eliminations, {{{{29, 1}}, {{6, 1}, {12, 1}}}}];


(* ::Subsubsection::Closed:: *)
(*Initial residual*)


a4\[Ellipsis]eliminations


a4\[Ellipsis]residual = Map[
	Function[elimination, 
		Expand[FullSimplify[Total[Join[
		Map[
			WeightedElement[eeCalc26[False], #[[1]], #[[2]]] &
			,elimination[[1]]
		],
		Map[
			WeightedElement[eeCalc26[True], #[[1]], #[[2]]] &
			,elimination[[2]]
		]
		]]]]
	]
	,a4\[Ellipsis]eliminations
];
eeCalc29 = a4\[Ellipsis]residual;
eeCalc29


(* ::Text:: *)
(*Hence, the initial residual is*)


Total[a4\[Ellipsis]residual]


(* ::Text:: *)
(*NOTE: the residual contains negative terms!*)


(* ::Text:: *)
(*Check to what extent are the components of a4 used / eliminated:*)


a4\[Ellipsis]positiveWeights = ConstantArray[0, Length[eeCalc26[False]]];
Map[
	Function[elimination, 
		Map[
			(a4\[Ellipsis]positiveWeights[[#[[1]]]] = a4\[Ellipsis]positiveWeights[[#[[1]]]] + #[[2]]) &
			,elimination[[1]]
		]
	]
	,a4\[Ellipsis]eliminations
];
a4\[Ellipsis]positiveWeights


(* ::Text:: *)
(*Check that all syntactically negative components have been eliminated*)


a4\[Ellipsis]negativeWeights = ConstantArray[0, Length[eeCalc26[True]]];
Map[
	Function[elimination, 
		Map[
			(a4\[Ellipsis]negativeWeights[[#[[1]]]] = a4\[Ellipsis]negativeWeights[[#[[1]]]] + #[[2]]) &
			,elimination[[2]]
		]
	]
	,a4\[Ellipsis]eliminations
];
a4\[Ellipsis]negativeWeights


(* ::Text:: *)
(*The weights describing the unused syntactically positive components*)


a4\[Ellipsis]remainingPositiveWeights = 1 - a4\[Ellipsis]positiveWeights


(* ::Text:: *)
(*Hence, a4 is the sum of the (not necessarily positive) residual and some positive terms*)


a4\[Ellipsis]2 = Total[a4\[Ellipsis]residual] + a4\[Ellipsis]remainingPositiveWeights . eeCalc26[False]


(* ::Text:: *)
(*Check*)


FullSimplify[a4\[Ellipsis]2 - a4\[Ellipsis]1]


(* ::Subsubsection::Closed:: *)
(*Further analysis to obtain a simplified form and residual containing -\[CapitalTheta]*)


(* ::Text:: *)
(*Our initial reductions led to*)


a4\[Ellipsis]residual


GroupBy[List @@ Expand[a4\[Ellipsis]residual], Internal`SyntacticNegativeQ]


(* ::Text:: *)
(*These are the unused positive terms in a4. Note that all terms that have been used in the above eliminations have been done so with weight 1.*)


eeCalc30 = Map[#[[1]] &,
Select[
	MapIndexed[
		If[#1 > 0, eeCalc27[[#2[[1]]]], None] &
		,a4\[Ellipsis]remainingPositiveWeights
	],
	ListQ
]]


(* ::Text:: *)
(*We have syntactically positive and negative terms*)


eeCalc31 = GroupBy[List @@ Total[Join[a4\[Ellipsis]residual, eeCalc30]], Internal`SyntacticNegativeQ]


(* ::Text:: *)
(*The positive terms are (scaled with I* \[Beta])*)


eeCalc32 = Map[
	# / Istar / \[Beta] &,
	eeCalc31[False]
];
eeCalc32


(* ::Text:: *)
(*We have 41 positive terms (scaled with I* \[Beta])*)


Length[eeCalc32]


(* ::Text:: *)
(*The negative terms are (scaled with I* \[Beta])*)


eeCalc33 = Map[
	# / Istar / \[Beta] &,
	eeCalc31[True]
];
eeCalc33


Grid[{{eeCalc32}, {eeCalc33}}]


(* ::Text:: *)
(*We carry out a series of simplifications*)


eeCalc34 = (\[Mu] + \[Rho]) * ((\[Gamma] + \[Mu]) * (\[Mu] + \[Kappa] * \[Omega] + \[Alpha] * \[Kappa]) + \[Alpha] * \[Omega] * \[Kappa]^2);


Simplify[Total[Join[Take[eeCalc32,{1, 8}],Take[eeCalc32, {31, 36}]]] - eeCalc34]


eeCalc35 = Simplify[Total[Take[eeCalc32, {9, 22}]]]


eeCalc36 = Simplify[Total[Join[Take[eeCalc32, {23, 24}],Take[eeCalc32, {37, 41}]]]]


eeCalc37 = Simplify[Total[Take[eeCalc32, {25, 30}]]]


(* ::Text:: *)
(*Now all positive terms have been accounted for*)


FullSimplify[
Total[eeCalc32] - 
(eeCalc34 + eeCalc35 + eeCalc36 + eeCalc37)
]


(* ::Text:: *)
(*The negative terms are*)


eeCalc38 = Simplify[Total[eeCalc33]]


(* ::Text:: *)
(*Together, we have*)


eeCalc39 = eeCalc34 + eeCalc35 + eeCalc36 + eeCalc37 + eeCalc38


(* ::Text:: *)
(*That is we have a concise form for a4*)


a4 = eeCalc39 * Istar * \[Beta]


(* ::Text:: *)
(*Check*)


FullSimplify[a4 - a4\[Ellipsis]1]


(* ::Text:: *)
(*Clearly the 2nd, 3rd and 5th terms are positive*)


Total[(List @@ eeCalc39)[[{2, 3, 5}]]]


(* ::Text:: *)
(*So - as an estimate - it is sufficient to consider the positivity of*)


Total[(List @@ eeCalc39)[[{1, 4}]]]


(* ::Text:: *)
(*That is actually -\[CapitalTheta]*)


FullSimplify[((
Total[(List @@ eeCalc39)[[{1, 4}]]] +
\[CapitalTheta]
) /. Join[Q0rule, Q1rule]) /. Join[\[Omega]rule, \[Eta]rule]]


(* ::Text:: *)
(*Hence, a4 > 0 follows for \[CapitalTheta] < 0.*)


(* ::Subsection::Closed:: *)
(*a4 (determinant) of the Jacobian*)


(* ::Subsubsection::Closed:: *)
(*Service code*)


TransformMatrix[matrix_, operation_, operand_] := Module[{result, resultFormula},
	Print["Transforming the matrix A:"];
	Print[matrix // MatrixForm];
	If[operation == "LeftMultiply",
		Print["\nMultiplying from the left by B:"];
		Print[operand // MatrixForm];
		Print["   where: |B| = "];
		Print[Det[operand]];
		resultFormula = "B x A";
		result = Simplify[operand . matrix];,
	If[operation == "RightMultiply",
		Print["\nMultiplying from the right by B:"];
		Print[operand // MatrixForm];
		Print["   where: |B| = "];
		Print[Det[operand]];
		resultFormula = "A x B";
		result = Simplify[matrix . operand];,
	If[operation == "Add",
		Print["\nAdding the matrix B:"];
		Print[(operand /. {EqSeq -> Seq, EqIeq -> Ieq, EqWeq -> Weq, EqJeq -> Jeq}) // MatrixForm];
		Print["   that is actually"];
		Print[(operand /. {EqSeq -> 0, EqIeq -> 0, EqWeq -> 0, EqJeq -> 0}) // MatrixForm];
		Print["   at the equilibrium."];
		resultFormula = "A + B";
		result = Simplify[matrix + (operand /. {EqSeq -> Seq, EqIeq -> Ieq, EqWeq -> Weq, EqJeq -> Jeq})];,
	If[operation == "Substitution",
		Print["\nSubstituting the rule(s):"];
		Print[operand[[2]] // MatrixForm];
		Print["   into position(s):"];
		Print["(" <> ToString[operand[[1]][[1]]] <> ", " <> ToString[operand[[1]][[2]]] <> ")"];
		resultFormula = "of the substitution";
		result = matrix;
		result[[operand[[1]][[1]], operand[[1]][[2]]]] = Simplify[matrix[[operand[[1]][[1]], operand[[1]][[2]]]] /. operand[[2]]];
	]
	]
	]
	];
	Print["\n------\n\nThe result " <> resultFormula <> " is: "];
	Print[result // MatrixForm];
	result
]


(* ::Subsubsection::Closed:: *)
(*Analysis*)


(* ::Text:: *)
(*The positivity of a4 is equivalent to the positivity of the determinant of the Jacobian evaluated at the unique endemic equilibrium (a4Matrix).*)


a4Matrix = Table[D[eqs[[i]], ees[[j]]], {i, 1, 4}, {j, 1, 4}];
a4Matrix // MatrixForm


workingMatrix = TransformMatrix[a4Matrix, "RightMultiply", 
	DiagonalMatrix[{Sstar, Istar, Wstar, Jstar}]
];


workingMatrix = TransformMatrix[workingMatrix, "RightMultiply", 
	{{1, 0, 0, 0}, {1, 1, 0, 0}, {1, 0, 1, 0}, {1, 0, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "Add", 
	{{- EqSeq, 0, 0, 0}, {- EqIeq, 0, 0, 0}, {- EqWeq, 0, 0, 0}, {- EqJeq, 0, 0, 0}}
];


workingMatrix = TransformMatrix[workingMatrix, "Substitution", 
	{{4, 4}, {Jstar -> J\[Ellipsis]ee\[Ellipsis]intermediate}}
];


workingMatrix = TransformMatrix[workingMatrix, "RightMultiply", 
	{{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 1, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "Add", 
	{{0, 0, 0, 0}, {0, - EqIeq, 0, 0}, {0, 0, 0, 0}, {0, 0, 0, 0}}
];


workingMatrix = TransformMatrix[workingMatrix, "LeftMultiply", 
	{{1, 1, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "LeftMultiply", 
	{{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 1}, {0, 0, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "LeftMultiply", 
	{{1, 0, 0, 0}, {0, 1 / Sstar / \[Beta], 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1 / Wstar / \[Beta] / \[Nu]}}
];


workingMatrix = TransformMatrix[workingMatrix, "LeftMultiply", 
	{{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, -1, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "RightMultiply", 
	{{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 1, 1, 0}, {0, 0, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "Add", 
	{{0, - EqSeq, 0, 0}, {0, 0, 0, 0}, {0, - EqWeq, 0, 0}, {0, 0, 0, 0}}
];


workingMatrix = TransformMatrix[workingMatrix, "RightMultiply", 
	{{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 1}, {0, 0, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "Add", 
	{{0, 0, 0, 0}, {0, 0, 0, 0}, {0, 0, 0, - EqWeq}, {0, 0, 0, 0}}
];


workingMatrix = TransformMatrix[workingMatrix, "LeftMultiply", 
	{{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1 / (Istar + Jstar * \[Xi])}}
];


workingMatrix = TransformMatrix[workingMatrix, "LeftMultiply", 
	{{1, 0, 0, 0}, {0, 1, 0, 0}, {- \[Alpha] * \[Kappa] / \[Mu], 0, 1, 0}, {0, 0, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "LeftMultiply", 
	{{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, \[Mu], 0}, {0, 0, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "LeftMultiply", 
	{{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, Wstar}}
];


workingMatrix = TransformMatrix[workingMatrix, "RightMultiply", 
	{{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1 / Wstar, 0}, {0, 0, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "RightMultiply", 
	{{\[Beta] * Sstar, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "Add", 
	{{0, 0, 0, 0}, {- EqIeq, 0, 0, 0}, {0, 0, 0, 0}, {0, 0, 0, 0}}
];


workingMatrix = TransformMatrix[workingMatrix, "Substitution", 
	{{2, 4}, {Jstar -> J\[Ellipsis]ee\[Ellipsis]intermediate}}
];


workingMatrix = TransformMatrix[workingMatrix, "LeftMultiply", 
	{{1, 0, 0, 0}, {0, (\[Mu] + \[Rho] - Wstar * \[Beta] * \[Nu] * \[Xi]) / Istar, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "LeftMultiply", 
	{{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, Wstar / \[Alpha] / \[Kappa], 0}, {0, 0, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "RightMultiply", 
	{{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, \[Alpha] * \[Kappa], 0}, {0, 0, 0, 1 / Wstar}}
];


workingMatrix = TransformMatrix[workingMatrix, "Substitution", 
	{{All, All}, {Sstar -> S\[Ellipsis]ee\[Ellipsis]intermediate, Istar -> I\[Ellipsis]ee\[Ellipsis]intermediate}}
];


workingMatrix = Simplify[Expand[workingMatrix]];
workingMatrix // MatrixForm


workingMatrix = TransformMatrix[workingMatrix, "LeftMultiply", 
	{{1, 0, 0, (\[Gamma] + \[Mu]) / (\[Mu] + \[Rho]) * \[Mu] * \[Nu] * \[Xi]}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "LeftMultiply", 
	{{1, \[Mu] / (\[Mu] + \[Rho]), 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "LeftMultiply", 
	{{0, 1, 0, 0}, {1, 0, 0, 0}, {0, 0, -1, 0}, {0, 0, 0, 1}}
];


workingMatrix = FullSimplify[Expand[workingMatrix]];
workingMatrix // MatrixForm


(* ::Text:: *)
(*The (3, 4) entry is linear in W*, let's force a simplification there.*)


workingMatrix[[3, 4]] = FullSimplify[CoefficientList[workingMatrix[[3, 4]], Wstar]] . {1, Wstar};
workingMatrix // MatrixForm


workingMatrix = TransformMatrix[workingMatrix, "RightMultiply", 
	{{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, - \[Gamma] * (\[Mu] * \[Nu] * \[Xi] / (\[Mu] + \[Rho]) + \[Kappa] * \[Omega] / (\[Gamma] + \[Mu])) / (\[Alpha] * \[Kappa] + \[Mu]) / (\[Mu] + \[Kappa] * \[Omega])}, {0, 0, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "LeftMultiply", 
	{{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1 / (\[Alpha] * \[Kappa] + \[Mu]) / (\[Mu] + \[Kappa] * \[Omega]), 0}, {0, 0, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "RightMultiply", 
	{{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, (\[Alpha] * \[Kappa] + \[Mu]) * (\[Mu] + \[Kappa] * \[Omega])}}
];


(* ::Text:: *)
(*(2, 4) looks overly complicated*)


FullSimplify[workingMatrix[[2, 4]]]


(* ::Text:: *)
(*One more "simplification" is *)


firstTerm = (\[Alpha] * \[Kappa] + \[Mu]) * (\[Mu] + \[Kappa] * \[Omega]) * (\[Beta] * \[Mu] * \[Nu] * \[Xi] / (\[Mu] + \[Rho]) + \[Kappa] * \[Omega]);
FullSimplify[FullSimplify[workingMatrix[[2, 4]]] - firstTerm] + firstTerm


workingMatrix[[2, 4]] = FullSimplify[FullSimplify[workingMatrix[[2, 4]]] - firstTerm] + firstTerm;
workingMatrix // MatrixForm


(* ::Text:: *)
(*We see two patterns repeating*)


F0rule = F0 -> (\[Gamma] + \[Mu]) * \[Mu] * \[Nu] * \[Xi] / (\[Mu] + \[Rho]) + \[Kappa] * \[Omega]


F2rule = F2 -> \[Beta] * \[Mu] * \[Nu] * \[Xi] / (\[Mu] + \[Rho]) + \[Kappa] * \[Omega]


workingMatrix = TransformMatrix[workingMatrix, "Substitution",
	{{2, 3}, {\[Xi] -> (\[Xi] /. First[Solve[(F0 /. F0rule) == F0, \[Xi]]])}}
];


workingMatrix = TransformMatrix[workingMatrix, "Substitution",
	{{4, 4}, {\[Xi] -> (\[Xi] /. First[Solve[(F0 /. F0rule) == F0, \[Xi]]])}}
];


(* ::Text:: *)
(*Again, (2, 4) seems to be a combination of F0 and F2, so we intervene manually as*)


workingMatrix[[2, 4]] = FullSimplify[Expand[(FullSimplify[FullSimplify[workingMatrix[[2, 4]]] - firstTerm] /. {\[Xi] -> (\[Xi] /. First[Solve[(F0 /. F0rule) == F0, \[Xi]]])})]] + 
	(firstTerm /. {\[Xi] -> (\[Xi] /. First[Solve[(F2 /. F2rule) == F2, \[Xi]]])});
workingMatrix // MatrixForm


workingMatrix = TransformMatrix[workingMatrix, "RightMultiply", 
	{{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, (\[Gamma] + \[Mu])}}
];


workingMatrix = TransformMatrix[workingMatrix, "LeftMultiply", 
	{{1, 0, 0, 0}, {0, 1, 0, - F0}, {0, 0, 1, 0}, {0, 0, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "RightMultiply", 
	{{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, \[Gamma], 0}, {0, 0, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "LeftMultiply", 
	{{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1 / \[Gamma], 0}, {0, 0, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "LeftMultiply", 
	{{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1 / Wstar, 0}, {0, 0, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "RightMultiply", 
	{{1, 0, 0, 0}, {0, 1 / Wstar, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "LeftMultiply", 
	{{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, - 1 / \[Alpha] / \[Gamma] / \[Kappa]}, {0, 0, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "RightMultiply", 
	{{1, 0, 0, 0}, {0, 0, -1, 0}, {0, 1, 0, 0}, {0, 0, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "LeftMultiply", 
	{{1, 0, 0, 0}, {0, 0, 0, 1}, {0, 1, 0, 0}, {0, 0, 1, 0}}
];


workingMatrix = TransformMatrix[workingMatrix, "RightMultiply", 
	{{1/((\[Gamma] + \[Mu])(\[Mu] - Wstar * \[Beta] * \[Nu] * \[Xi] + \[Rho])), 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "RightMultiply", 
	{{1, 0, 0, 0}, {0, 1/(\[Alpha] * \[Gamma] * \[Kappa]), 0, 0}, {0, 0, 1, 0}, {0, 0, 0, 1}}
];


F1rule = F1 -> ((F0 +(\[Mu] * (\[Beta] - \[Gamma] - \[Mu]))/(Wstar * \[Beta])) /. F0rule)


FullSimplify[Last[F1rule] - (((\[Gamma] + \[Mu]) + (\[Beta] - \[Gamma] - \[Mu]) * (\[Rho] + \[Mu]) / (\[Beta] * \[Nu] * \[Xi] * Wstar)) * \[Mu] * \[Nu] * \[Xi] / (\[Rho] + \[Mu]) + \[Omega] * \[Kappa])]


workingMatrix = TransformMatrix[workingMatrix, "Substitution",
	{{All, All}, {F0 -> F1 - (\[Mu] * (\[Beta] - \[Gamma] - \[Mu]))/(Wstar * \[Beta])}}
];


workingMatrix = TransformMatrix[workingMatrix, "RightMultiply", 
	{{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1/F1, 0}, {0, 0, 0, 1}}
];


workingMatrix = TransformMatrix[workingMatrix, "LeftMultiply", 
	{{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, 0, F1 * \[Alpha] * \[Gamma] * \[Kappa]}}
];


workingMatrix = TransformMatrix[workingMatrix, "LeftMultiply", 
	{{1, 0, 0, 0}, {0, 1, 0, 0}, {0, 0, 1, 0}, {0, 0, -1, 1}}
];


(* ::Text:: *)
(*Dealing with (1, 4) now*)


Q1 /. Q1rule


((Q1 /. Q1rule) * \[Mu] / (\[Rho] + \[Mu]) + \[Eta] * \[Kappa]^2 * \[Gamma]) 


FullSimplify[((Q1 /. Q1rule) * \[Mu] / (\[Rho] + \[Mu]) + \[Eta] * \[Kappa]^2 * \[Gamma]) / (\[Gamma] + \[Mu])]


FullSimplify[(
workingMatrix[[1,4]] - 
\[Beta] * \[Nu] * \[Xi] * (Q1 * \[Mu] / (\[Rho] + \[Mu]) + \[Eta] * \[Kappa]^2 * \[Gamma]) 
/. Q1rule) /. Join[\[Omega]rule, \[Eta]rule]]


workingMatrix = TransformMatrix[workingMatrix, "Substitution",
	{{1, 4}, {(\[Gamma] + \[Mu]) * (\[Alpha] * \[Kappa] + \[Mu]) * (\[Mu] + \[Kappa] * \[Omega]) -> Q1 * \[Mu] / (\[Rho] + \[Mu]) + \[Eta] * \[Kappa]^2 * \[Gamma]}}
];


workingMatrix = TransformMatrix[workingMatrix, "Substitution",
	{{3, 4}, {(\[Gamma] + \[Mu]) * (\[Alpha] * \[Kappa] + \[Mu]) * (\[Mu] + \[Kappa] * \[Omega]) -> Q1 * \[Mu] / (\[Rho] + \[Mu]) + \[Eta] * \[Kappa]^2 * \[Gamma]}}
];


workingMatrix = TransformMatrix[workingMatrix, "Substitution",
	{{4, 4}, {(\[Gamma] + \[Mu]) * (\[Alpha] * \[Kappa] + \[Mu]) * (\[Mu] + \[Kappa] * \[Omega]) -> Q1 * \[Mu] / (\[Rho] + \[Mu]) + \[Eta] * \[Kappa]^2 * \[Gamma]}}
];


workingMatrix = TransformMatrix[workingMatrix, "Substitution",
	{{2, 4}, {\[Alpha] * \[Gamma] * \[Kappa] -> Q0}}
];


workingMatrix = TransformMatrix[workingMatrix, "Substitution",
	{{4, 4}, {\[Alpha] * \[Gamma] * \[Kappa] -> Q0}}
];


Det[workingMatrix]


(* ::Text:: *)
(*We see that F1 > F2 > 0 when R0 > 1 as*)


Reduce[Join[parameterAssumptions,{\[Rho] + \[Mu] > \[Nu] * \[Beta] * \[Xi] * Wstar > 0, Wstar > 0, (F1 /. F1rule) > (F2 /. F2rule)}]]


(* ::Text:: *)
(*So it is sufficient to consider R0 > 1 and F2 only (replace F1 with F2)*)


Simplify[(Det[workingMatrix] /. F1 -> F2) / F2]


Expand[Simplify[(Det[workingMatrix] /. F1 -> F2) / F2] /. F2rule]


Simplify[(Expand[Simplify[(Det[workingMatrix] /. F1 -> F2) / F2] /. F2rule]) /. Q0 * \[Kappa] * \[Omega] -> \[Eta] * \[Gamma] * \[Kappa]^2]


Simplify[Simplify[(Expand[Simplify[(Det[workingMatrix] /. F1 -> F2) / F2] /. F2rule]) /. Q0 * \[Kappa] * \[Omega] -> \[Eta] * \[Gamma] * \[Kappa]^2] * (\[Rho] + \[Mu]) / \[Mu]]


\[CapitalTheta]


(* ::Text:: *)
(*Hence, a4 > 0 follows for \[CapitalTheta] > 0.*)


(* ::Subsection::Closed:: *)
(*Listing of the 'simplified' coefficients*)


a1


a2


a3


a4
