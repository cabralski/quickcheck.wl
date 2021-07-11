(* ::Package:: *)

(* ::Title:: *)
(*QuickCheck.wl \[LongDash] 0.1.0*)


(* ::Author:: *)
(*Pedro Gomes Cabral \[LongDash] 2021, MIT Licensed.*)


(* ::Text:: *)
(*A package for property-based-testing for the Wolfram Language.*)


BeginPackage["QuickCheck`"];


(* ::Subtitle:: *)
(**)


(* ::Section:: *)
(*Messages*)


QuickCheck::usage = "QuickCheck[\"name\", property, \"Assume\" -> {variable -> type..}, \"Given\" -> {condition..}}] checks if the property is valid assuming the types of the values from \"Assume\" and the conditions from \"Given\".";


QuickCheck::invargs = "Invalid arguments, QuickCheck must be called with a name, property (equality or inequality), and assumptions.";


QuickCheck::bool = "The property \"``\" always yields ``.";


QuickCheck::notcmp = "The property \"``\" could not yield a boolean result on \"``\" (uncomparable, cannot cast to Boolean).";


(* ::Section:: *)
(*Types*)


\[CapitalTau]Any::usage = "";


\[CapitalTau]PlainText::usage = "";
\[CapitalTau]ASCII::usage = "";
\[CapitalTau]UTF8::usage = "";


\[CapitalTau]Boolean::usage = "";


\[CapitalTau]PositiveInteger::usage = "";
\[CapitalTau]Integer::usage = "";
\[CapitalTau]NegativeInteger::usage = "";


\[CapitalTau]PositiveDecimal::usage = "";
\[CapitalTau]Decimal::usage = "";
\[CapitalTau]NegativeDecimal::usage = "";


\[CapitalTau]Rule::usage = "";


\[CapitalTau]List::usage = "";
\[CapitalTau]NonEmptyList::usage = "";
\[CapitalTau]MissingList::usage = "";


\[CapitalTau]Association::usage = "";


(* ::Subtitle:: *)
(**)


Begin["`Private`"];


(* ::Subtitle:: *)
(**)


(* ::Section:: *)
(*Utilities*)


ComparableQ[any_] := MemberQ[{Integer, Real, String, Complex, List}, Head[any]]


(* ::Subtitle:: *)
(**)


(* ::Section:: *)
(*Constant Global Variables*)


PlainChars = Join[CharacterRange[65, 90], CharacterRange[97, 122], {" ", " ", " ", " ", " "}];


UTF8Chars = CharacterRange[0, 65536];


ASCIIChars = CharacterRange[0, 127];


(* ::Subtitle:: *)
(**)


(* ::Section:: *)
(*Properties*)


SetAttributes[QuickCheck, HoldAll];


Options[QuickCheck] = {
	"Examples" -> {},
	
	"Runs" -> 1024,
	"MaxFails" -> 1,
	
	"ExponentRange" -> 16,
	
	"MinMaxStringSize" -> {0, 32},
	"MinMaxListSize" -> {0, 32}
};


SyntaxInformation[QuickCheck] = {
	"ArgumentsPattern" -> {_, _, _, OptionsPattern[]},
	"OptionNames" -> Keys[Options[QuickCheck]]
};


(* ::Subtitle:: *)
(**)


(* ::Section:: *)
(*Implementation*)


QuickCheck[
	
	(* Name of the property to be checked. *)
	name_String,
	
	(* Actual property. The expression is hold. *)
	(
	property_Equal|
	property_Unequal|
	
	property_And|
	property_Or|
	property_Xor|
	property_Nor|
	property_Not|
	property_Nand|
	
	property_Implies|
	property_Equivalent|
	
	property_Greater|
	property_Less|
	
	property_GreaterEqual|
	property_LessEqual
	),
	
	(* Assumptions and conditions. *)
	"Assume" -> assumptions_List,
	
	(* Examples and options. *)
	opts : OptionsPattern[]
	
] := Module[{
	
	(* Option values. *)
	examples = OptionValue["Examples"],
	runs = OptionValue["Runs"],
	maxfails = OptionValue["MaxFails"],
	
	(* Range options. *)
	erange = OptionValue["ExponentRange"],
	mmstring = OptionValue["MinMaxStringSize"],
	mmlist = OptionValue["MinMaxListSize"],
	
	(* Local counters. *)
	fails = 0,
	currentrun = -1,
	
	(* Local variables. *)
	mutassume = None,
	testmonitor = "",
	falsifiables = {},
	computedvalue = None,
	notcomparable = False,
	
	(* Time variables. *)
	qcstart = None,
	qcend = None,
	
	(* Finished flag. *)
	qcfinished = False

},
	
	(* Check if the property always yields a constant boolean. *)
	If[property == True || property == False,
		Return[Message[QuickCheck::bool, HoldForm[property], property]];
	];
	
	(* Print temporary message. *)
	PrintTemporary[
		StringForm["Quickchecking property \"``\"", name], ProgressIndicator[Appearance -> "Ellipsis"]
	];
	
	(* Start timing! *)
	qcstart = Now;
	
	(* For every run.. *)
	Do[
		
		(* Check if the property was not comparable. *)
		If[fails >= maxfails,
			Break[]
		];
		
		(* Add one to current run. *)
		currentrun += 1;
		
		(* Replace types with actual values. *)
		mutassume = assumptions //. {
			\[CapitalTau]Any :> RandomChoice[{"ASCII", "Decimal", "Integer", "Boolean"}],
		
			\[CapitalTau]PlainText :> StringJoin@RandomChoice[PlainChars, RandomInteger[mmstring]],
			\[CapitalTau]ASCII :> StringJoin@RandomChoice[ASCIIChars, RandomInteger[mmstring]],
			\[CapitalTau]UTF8 :> StringJoin@RandomChoice[UTF8Chars, RandomInteger[mmstring]],
			
			\[CapitalTau]Boolean :> RandomChoice[{True, False}],
			
			\[CapitalTau]PositiveInteger :> RandomChoice[{0, RandomInteger[{0, 2^erange}]}],
			\[CapitalTau]Integer :> RandomChoice[{0, RandomInteger[{-2^erange, 2^erange}]}],
			\[CapitalTau]NegativeInteger :> RandomChoice[{-1, RandomInteger[{-2^erange, -1}]}],
			
			\[CapitalTau]PositiveDecimal :> RandomChoice[{0.0, RandomReal[{0, 2.0^erange}]}],
			\[CapitalTau]Decimal :> RandomChoice[{0.0, RandomReal[{-2.0^erange, 2.0^erange}]}],
			\[CapitalTau]NegativeDecimal :> RandomChoice[{$MinMachineNumber, RandomReal[{-2.0^erange, $MinMachineNumber}]}],
			
			\[CapitalTau]Rule[type_, type_] :> type -> type,
			\[CapitalTau]Rule[type_] :> "PlainText" -> type,
			
			\[CapitalTau]List[type_] :> Table[type, RandomInteger[mmlist]],
			\[CapitalTau]NonEmptyList[type_] :> Table[type, RandomInteger[{1, mmlist[[2]]}]],
			\[CapitalTau]MissingList[type_] :> Table[RandomChoice[{type, Missing["NotAvailable"]}], RandomInteger[mmlist]],
			
			\[CapitalTau]Association[type_] :> Association@Table["PlainText" -> type, RandomInteger[mmlist]],
			\[CapitalTau]Association[type_, type_] :> Association@Table[type -> type, RandomInteger[mmlist]]
		};
			
		(* Replace the mutable assumption with itself. *)
		mutassume = Normal[AssociationThread[Keys[mutassume] -> (ReplaceRepeated[mutassume][Values[mutassume]])]];
			
		(* Compute the expression. *)
		computedvalue = ReleaseHold[Hold[property] //. mutassume];
			
		(* Check if the replaced assumption on the property works. *)
		If[computedvalue,
				
			(* If the property passes, okay! *)
			If[Mod[run, 100] == 0,
				PrintTemporary[StringForm["Passed `` times..", run]];
			];
			Continue[],
				
			(* If it fails.. *)
			fails += 1;
			If[Mod[fails, 100] == 0,
				PrintTemporary[StringForm["Failed `` times..", fails]];
			];
			AppendTo[falsifiables, Inactivate[property] /. mutassume];
			Continue[]
				
		];
			
		(* The comparison could not be completed. *)
		notcomparable = True;
		Break[]
		
	, {run, 0, runs - 1}];
	
	(* End of QuickCheck! *)
	qcend = Now; qcfinished = False;
	
	(* Raise an error because it could not compare a property. *)
	If[notcomparable,
		Return[Message[QuickCheck::notcmp, name, computedvalue]];
	];
	
	(* Print "Okay!" or "Falsifiable". *)
	If[fails > 0,
		Echo[StringForm["Falsifiable after `` test(s) on ``.", Min[{currentrun + 1, runs}], ToString[qcend - qcstart]]],
		Echo[StringForm["Okay! Property \"``\" passed `` test(s) on ``.", Style[name, Bold], runs, ToString[qcend - qcstart]]]
	];
	
	(* Return falsifiables. *)
	Return[falsifiables]
	
];


QuickCheck[args___] := Message[QuickCheck::invargs];


(* SetAttributes[QuickCheck, {Protected, ReadProtected}]; *)


(* ::Subtitle:: *)
(**)


End[];


EndPackage[];
