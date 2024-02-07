### Blueprint computations for A_3
# A "term" is a record with 2 or 3 entries. The first entry is a string that describes the type of the term and which is called "type". The remaining entries (which are called "sub" if there is only one or "subLeft" and "subRight" if there are two) store the information which describes the term.
# We document the types in the following format:
# "Type string" [number of additional record entries]: Description of the type. In this description, "term1" and "term2" represent the additional record entries.

## Documentation of the types of terms.
# "Indet" [1]: An indeterminate. The second list entry is a string s. Represents the indeterminate with the name s.
# "Integer" [2]: An integer. The second list entry is an integer i. Represents the integer i.
# "RingMinus" [1]: A minus sign (in the ring). Represents -term1.
# "RingSum" [2]: A sum of two terms (in the ring). Represents term1 + term2.
# "RingMult" [2]: A product of two terms (in the ring). Represents term1 * term2.

## Constructors for the various types of terms

IndetForString := function(string)
	return rec( type := "Indet", sub := string );
end;

IndetForInt := function(n)
	return rec( type := "Integer", sub := n );
end;

RingMinus := function(term)
	if term.type = "RingMinus" then
		return term.sub;
	else
		return rec( type := "RingMinus", sub := term );
	fi;
end;



RingAdd := function(term1, term2)
	return rec(type := "RingSum", subLeft := term1, subRight := term2);
end;


RingMult := function(term1, term2)
	return rec( type := "RingMult", subLeft := term1, subRight := term2);
end;

ZeroTerm := IndetForInt(0);

## "Plug in zero" functions

# term: A term.
# indet: A string.
# Output: The term obtained from the input term by replacing the indeterminate with name indet by 0.
PlugInZero := function(term, indet)
	local type, func, addFunc, newTerm, newTerm1, newTerm2;
	type := term.type;
	if type = "Indet" then
		if term.sub = indet then
			return ZeroTerm;
		else
			return StructuralCopy(term);
		fi;
	elif type = "Integer" then
		return StructuralCopy(term);
	elif type = "RingMinus" or type = "ModMinus" or type = "ModInv" then
		if type = "RingMinus" then
			func := RingMinus;
		elif type = "ModMinus" then
			func := ModMinus;
		elif type = "ModInv" then
			func := ModInv;
		fi;
		newTerm := PlugInZero(term.sub, indet);
		if newTerm = ZeroTerm then
			return ZeroTerm; # -0 = 0 or 0^ = 0
		else
			return func(newTerm);
		fi;
	elif type = "RingSum" or type = "ModSum" then
		if type = "RingSum" then
			addFunc := RingAdd;
		elif type = "ModSum" then
			addFunc := ModAdd;
		fi;
		newTerm1 := PlugInZero(term.subLeft, indet);
		newTerm2 := PlugInZero(term.subRight, indet);
		if newTerm1 = ZeroTerm and newTerm2 = ZeroTerm then
			return ZeroTerm;
		elif newTerm1 <> ZeroTerm and newTerm2 <> ZeroTerm then
			return addFunc(newTerm1, newTerm2);
		elif newTerm1 = ZeroTerm then
			return newTerm2;
		else
			return newTerm1;
		fi;
	elif type = "RingMult" or type = "q" or type = "f" or type = "g" then
		if type = "RingMult" then
			func := RingMult;
		elif type = "q" then
			func := q;
		elif type = "f" then
			func := f;
		elif type = "g" then
			func := g;
		fi;
		newTerm1 := PlugInZero(term.subLeft, indet);
		newTerm2 := PlugInZero(term.subRight, indet);
		if newTerm1 = ZeroTerm or newTerm2 = ZeroTerm then
			return ZeroTerm;
		else
			return func(newTerm1, newTerm2);
		fi;
	fi;
end;

# Same as PlugInZero, but indetList is a list and all indeterminates in this list are put to zero.
PlugInZeroList := function(term, indetList) 
	local result, indet;
	result := term;
	for indet in indetList do
		result := PlugInZero(result, indet);
	od;
	return result;
end;

## Functions for converting a term to a string

# Returns the input string in (LaTeX) brackets
inBrackets := function(string)
	return Concatenation("\\brackets{", string, "}");
end;

# Returns a (LaTeX) string which represents term.
TermAsString := function(term)
	local type, substring, string1, string2, substring1, substring2, funcString, argument, subtype, subtype1, subtype2;
	type := term.type;
	if type = "Indet" or type = "Integer" then
		return String(term.sub);
	elif type = "RingMinus" or type = "ModMinus" then
		subtype := term.sub.type;
		if subtype = "RingSum" or subtype = "ModSum" then
			return Concatenation("-", inBrackets(TermAsString(term.sub)));
		elif subtype = "RingMinus" or subtype = "ModMinus" then # -- = +
			return TermAsString(term.sub.sub);
		else
			return Concatenation("-", TermAsString(term.sub));
		fi;
	elif type = "RingSum" or type = "ModSum" then
		string1 := TermAsString(term.subLeft);
		string2 := TermAsString(term.subRight);
		subtype2 := term.subRight.type;
		if subtype2 = "RingMinus" or subtype2 = "ModMinus" then # +- = -
			return Concatenation(string1, string2);
		else
			return Concatenation(string1, "+", string2);
		fi;
	elif type = "RingMult" then
		substring1 := TermAsString(term.subLeft);
		subtype1 := term.subLeft.type;
		substring2 := TermAsString(term.subRight);
		subtype2 := term.subRight.type;
		if subtype1 in ["RingSum", "RingMult", "RingMinus"] then
			string1 := inBrackets(substring1);
		else
			string1 := substring1;
		fi;
		if subtype2 in ["RingSum", "RingMult", "RingMinus"] then
			string2 := inBrackets(substring2);
		else
			string2 := substring2;
		fi;
		return Concatenation(string1, string2);
	elif type = "RingInv" then
		substring := TermAsString(term.sub);
		subtype := term.sub.type;
		if subtype = "RingSum" or subtype = "RingMult" then
			return RingInvOnString(inBrackets(substring));
		else
			return RingInvOnString(substring);
		fi;
	elif type = "ModInv" then
		substring := TermAsString(term.sub);
		return ModInvOnString(substring);
	elif type = "q" or type = "f" or type = "g" then
		if type = "q" then
			funcString := "q";
		elif type = "f" then
			funcString := "f";
		elif type = "g" then
			funcString := "g";
		fi;
		string1 := TermAsString(term.subLeft);
		string2 := TermAsString(term.subRight);
		argument := inBrackets(Concatenation(string1, ",", string2));
		return Concatenation(funcString, argument);
	else
		return fail;
	fi;
end;

## Rewriting rules

rule121 := function(list, startindex)
	local a, b, c, transformedList;
	transformedList := StructuralCopy(list);
	a := list[startindex];
	b := list[startindex+1];
	c := list[startindex+2];
	transformedList[startindex] := c;
	transformedList[startindex+1] := RingAdd(RingMinus(b), RingMinus(RingMult(c, a)));
	transformedList[startindex+2] := a;
	return transformedList;
end;

rule212 := function(list, startindex)
	local a, b, c, transformedList;
	transformedList := StructuralCopy(list);
	a := list[startindex];
	b := list[startindex+1];
	c := list[startindex+2];
	transformedList[startindex] := c;
	transformedList[startindex+1] := RingAdd(RingMinus(b), RingMinus(RingMult(a, c)));
	transformedList[startindex+2] := a;
	return transformedList;
end;

# rule13to31 and rule31to13
ruleSwitch := function(list, startindex)
	local a, b, transformedList;
	transformedList := StructuralCopy(list);
	transformedList[startindex] := list[startindex+1];
	transformedList[startindex+1] := list[startindex];
	return transformedList;
end;



blueA := function()
	local list, list0, listUp, listDown, i, outputFile;
	outputFile := OutputTextFile("Desktop/A-Blue.tex", false);
	SetPrintFormattingStatus(outputFile, false);
	PrintTo(outputFile); # Make file empty
	
	## In the following, each list has 6 elements, all of which are terms.
	# list0 is a list of 6 indeterminates.
	list0 := List([ "a", "b", "c", "d", "e", "f" ], x -> IndetForString(x));
	
	## "Working halfway down"
	# 1
	listDown := ruleSwitch(list0, 3);
	# 2
	listDown := rule121(listDown, 1);
	# 3
	listDown := rule121(listDown, 3);
	# 4
	listDown := ruleSwitch(listDown, 2);
	listDown := ruleSwitch(listDown, 5);
	# 5
	listDown := rule121(listDown, 3);
	# 6
	listDown := rule121(listDown, 1);

	## "Working halfway up"
	# 13
	listUp := rule121(list0, 4);
	# 12
	listUp := rule121(listUp, 2);
	# 11
	listUp := ruleSwitch(listUp, 1);
	listUp := ruleSwitch(listUp, 4);
	# 10
	listUp := rule121(listUp, 2);
	# 9
	listUp := rule121(listUp, 4);
	# 8
	listUp := ruleSwitch(listUp, 3);
	
	## Create a basic LaTeX file from the result
	AppendTo(outputFile, "\\documentclass[a4paper,11pt]{article}\n");
	AppendTo(outputFile, "\\usepackage[left=2.5cm,right=2cm,top=2.5cm,bottom=2cm]{geometry}\n");
	AppendTo(outputFile, "\\newcommand{\\brackets}[1]{(#1)}\n\n");
	AppendTo(outputFile, "\\begin{document}\n");
	for i in [1..6] do
		AppendTo(outputFile, "\t\\textbf{", i, ". column:}\n\n");
		AppendTo(outputFile, "\t\\addvspace{0.1cm}\n");
		AppendTo(outputFile, "\t(1) -- (12): $ ", TermAsString(listDown[i]), " $\n\n");
		AppendTo(outputFile, "\t(23) -- (12): $ ", TermAsString(listUp[i]), " $");
		if i < 6 then
			AppendTo(outputFile, "\n\n\t\\addvspace{0.4cm}");
		fi;
	od;
	AppendTo(outputFile, "\n\\end{document}");
	return [ listDown, listUp];
end;

## Some tests.

test121 := function()
	local list0, list1, i;
	list0 := List(["a", "b", "c"], x -> IndetForString(x));
	list1 := rule121(list0, 1);
	for i in [1..3] do
		Display(TermAsString(list1[i]));
	od;
end;

test212 := function()
	local list0, list1, i;
	list0 := List(["a", "b", "c"], x -> IndetForString(x));
	list1 := rule212(list0, 1);
	for i in [1..3] do
		Display(TermAsString(list1[i]));
	od;
end;

testSwitch := function()
	local list0, list1, i;
	list0 := List(["a", "b"], x -> IndetForString(x));
	list1 := ruleSwitch(list0, 1);
	for i in [1..2] do
		Display(TermAsString(list1[i]));
	od;
end;
