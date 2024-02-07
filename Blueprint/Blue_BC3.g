### Blueprint computations for B_3
# A "term" is a record with 2 or 3 entries. The first entry is a string that describes the type of the term and which is called "type". The remaining entries (which are called "sub" if there is only one or "subLeft" and "subRight" if there are two) store the information which describes the term.
# We document the types in the following format:
# "Type string" [number of additional record entries]: Description of the type. In this description, "term1" and "term2" represent the additional record entries.

## Documentation of the types of terms.
# "Indet" [1]: An indeterminate. The second record entry is a string s. Represents the indeterminate with the name s.
# "Integer" [2]: An integer. The second record entry is an integer i. Represents the integer i.
# "RingMinus" [1]: A minus sign (in the ring). Represents -term1.
# "RingSum" [2]: A sum of two terms (in the ring). Represents term1 + term2.
# "ModSum" [2]: A sum of two terms (in the module). Represents term1 + term2.
# "RingMult" [2]: A product of two terms (in the ring). Represents term1 * term2.
# "RingInv" [1]: The ring involution x -> x'. Represents (term1)'.
# "ModInv" [1]: The module involution x -> x^. Represents (term1)^.
# "phi" [2]: The map phi. Represents phi(term1, term2).
# "Tr" [2]: The map Tr. Represents Tr(term1, term2).
# "pi" [2]: The map pi. Represents pi(term1, term2).
# "psi" [2]: The map psi. Represents psi(term1, term2).

## Constructors for the various types of terms
IndetForString := function(string)
	return rec( type := "Indet", sub := string );
end;

IndetForInt := function(n)
	return rec( type := "Integer", sub := n );
end;

RingSum := function(term1, term2)
	return rec( type := "RingSum", subLeft := term1, subRight := term2 );
end;

ModSum := function(term1, term2)
	return rec( type := "ModSum", subLeft := term1, subRight := term2 );
end;

RingMinus := function(term)
	if term.type = "RingMinus" then
		return term.sub;
	elif term.type = "RingSum" then
		return RingSum(RingMinus(term.subLeft), RingMinus(term.subRight));
	else
		return rec( type := "RingMinus", sub := term );
	fi;
end;

ModMinus := function(term)
	if term.type = "ModMinus" then
		return term.sub;
	elif term.type = "ModSum" then
		return ModSum(ModMinus(term.subLeft), ModMinus(term.subRight));
	else
		return rec( type := "ModMinus", sub := term );
	fi;
end;



RingMult := function(term1, term2)
	return rec( type := "RingMult", subLeft := term1, subRight := term2 );
end;

RingInv := function(term)
	if term.type = "RingInv" then
		return term.sub; # x'' = x
	elif term.type = "RingSum" then
		return RingSum(RingInv(term.subLeft), RingInv(term.subRight)); # (x+y)' = x' + y'
	elif term.type = "RingMinus" then
		return RingMinus(RingInv(term.sub)); # (-x)' = -x'
	else
		return rec( type := "RingInv", sub := term );
	fi;
end;

ModInv := function(term)
	if term.type = "ModInv" then
		return term.sub; # x^^ = x
	elif term.type = "ModSum" then
		return ModSum(ModInv(term.subLeft), ModInv(term.subRight)); # (x+y)^ = x^ + y^
	elif term.type = "ModMinus" then
		return ModMinus(ModInv(term.sub)); # (-x)^ = -x^
	else
		return rec( type := "ModInv", sub := term );
	fi;
end;

phi := function(term1, term2)
	return rec( type := "phi", subLeft := term1, subRight := term2 );
end;

Tr := function(term1, term2)
	return rec( type := "Tr", subLeft := term1, subRight := term2 );
end;

pi := function(term1, term2)
	return rec( type := "pi", subLeft := term1, subRight := term2 );
end;

psi := function(term1, term2)
	return rec( type := "psi", subLeft := term1, subRight := term2 );
end;

ZeroTerm := rec( type := "Integer", sub := 0 );

## Functions for "plugging in" zero in a term

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
	elif type = "RingMinus" or type = "ModMinus" or type = "RingInv" or type = "ModInv" then
		if type = "RingMinus" then
			func := RingMinus;
		elif type = "ModMinus" then
			func := ModMinus;
		elif type = "RingInv" then
			func := RingInv;
		elif type = "ModInv" then
			func := ModInv;
		fi;
		newTerm := PlugInZero(term.sub, indet);
		if newTerm = ZeroTerm then
			return ZeroTerm; # -0 = 0 or 0' = 0 or 0^ = 0
		else
			return func(newTerm);
		fi;
	elif type = "RingSum" or type = "ModSum" then
		if type = "RingSum" then
			addFunc := RingSum;
		elif type = "ModSum" then
			addFunc := ModSum;
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
	elif type = "RingMult" or type = "phi" or type = "Tr" or type = "pi" or type = "psi" then
		if type = "RingMult" then
			func := RingMult;
		elif type = "phi" then
			func := phi;
		elif type = "Tr" then
			func := Tr;
		elif type = "pi" then
			func := pi;
		elif type = "psi" then
			func := psi;
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

# Puts all indeterminates to 0 except for the ones in indetlist, and returns the result as a string
PlugInZeroExcept := function(term, indetList)
	local zeroList, indet;
	zeroList := [];
	for indet in [ "u", "v", "w", "a", "b", "c", "d", "r", "s" ] do
		if not indet in indetList then
			Add(zeroList, indet);
		fi;
	od;
	return TermAsString(PlugInZeroList(term, zeroList));
end;

## Functions for converting a term to a string

# If bSimpleOutputMode = false, then the output string is intended for use in LaTeX.
# Otherwise the output string is intended to be easily readable.
bSimpleOutputMode := false;

# Returns the input string in brackets
inBrackets := function(string)
	if bSimpleOutputMode = true then
		return Concatenation("(", string, ")");
	else
		return Concatenation("\\brackets{", string, "}");
	fi;
end;

# Returns a string which is used to represent terms of type "type".
TypeSymbol := function(type)
	if bSimpleOutputMode = true then
		if type = "RingSum" or type = "ModSum" then
			return "+";
		elif type = "RingMinus" or type = "ModMinus" then
			return "-";
		elif type in [ "phi", "Tr", "pi", "psi" ] then
			return type;
		fi;
	else
		if type = "RingSum" then
			return "+";
		elif type = "ModSum" then
			return "\\joradd ";
		elif type = "RingMinus" then
			return "-";
		elif type = "ModMinus" then
			return "\\jormin ";
		elif type = "phi" then
			return "\\jorsc";
		elif type = "Tr" then
			return "\\jorTr";
		elif type = "pi" then
			return "\\jorproj";
		elif type = "psi" then
			return "\\psi";
		fi;
	fi;
end;

# Returns the ring involution applied to the string.
RingInvOnString := function(string)
	if bSimpleOutputMode = true then
		return Concatenation("\rinv{", string, "}");
	else
		return Concatenation("\\rinv{", string, "}");
	fi;
end;

# Returns the module involution applied to the string.
ModInvOnString := function(string)
	if bSimpleOutputMode = true then
		return Concatenation("\minv{", string, "}");
	else
		return Concatenation("\\modinv{", string, "}");
	fi;
end;

# Returns a (LaTeX) string which represents term.
TermAsString := function(term)
	local type, substring, string1, string2, substring1, substring2, funcString, argument, subtype, subtype1, subtype2, symbol;
	type := term.type;
	if type = "Indet" or type = "Integer" then
		return String(term.sub);
	elif type = "RingMinus" or type = "ModMinus" then
		subtype := term.sub.type;
		substring := TermAsString(term.sub);
		symbol := TypeSymbol(type);
		if subtype = "RingSum" or subtype = "ModSum" then
			return Concatenation(symbol, inBrackets(substring));
		elif subtype = "RingMinus" or subtype = "ModMinus" then # -- = +
			return TermAsString(term.sub.sub);
		else
			return Concatenation(symbol, substring);
		fi;
	elif type = "RingSum" or type = "ModSum" then
		string1 := TermAsString(term.subLeft);
		string2 := TermAsString(term.subRight);
		subtype2 := term.subRight.type;
		symbol := TypeSymbol(type);
		if subtype2 = "RingMinus" or subtype2 = "ModMinus" then # +- = -
			return Concatenation(string1, string2);
		else
			return Concatenation(string1, symbol, string2);
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
		if subtype in [ "RingSum", "RingMult", "RingMinus" ]  then
			return RingInvOnString(inBrackets(substring));
		else
			return RingInvOnString(substring);
		fi;
	elif type = "ModInv" then
		substring := TermAsString(term.sub);
		return ModInvOnString(substring);
	elif type in [ "phi" , "Tr" , "pi" , "psi" ] then
		symbol := TypeSymbol(type);
		string1 := TermAsString(term.subLeft);
		string2 := TermAsString(term.subRight);
		argument := inBrackets(Concatenation(string1, ",", string2));
		return Concatenation(symbol, argument);
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
	transformedList[startindex+1] := RingSum(RingMinus(b), RingMinus(RingMult(c, a)));
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
	transformedList[startindex+1] := RingSum(RingMinus(b), RingMinus(RingMult(a, c)));
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

rule3232 := function(list, startindex)
	local u, v, a, b, uInv, vInv, aInv, bInv, transformedList;
	transformedList := StructuralCopy(list);
	v := list[startindex];
	a := list[startindex+1];
	u := list[startindex+2];
	b := list[startindex+3];
	aInv := RingInv(a);
	bInv := RingInv(b);
	vInv := ModInv(v);
	uInv := ModInv(u);
	transformedList[startindex] := bInv;
	transformedList[startindex+1] := ModSum(ModSum(ModInv(phi(vInv, RingMinus(bInv))), u), ModInv(Tr(b, aInv)));
	transformedList[startindex+2] := RingSum(RingSum(RingMinus(pi(vInv, b)), RingMinus(aInv)), RingMinus(psi(ModSum(phi(vInv, RingMinus(bInv)), uInv), vInv)));
	transformedList[startindex+3] := vInv;
	return transformedList;
end;

## This functions performs the blueprint computation and writes the result of this computation to a file "BC-Blue.txt" on the desktop. The "writing to file"-stuff works on my Windows system, your mileage may vary.
blueBC := function()
	local list, list0, listUp, listDown, i, outputFile;
	outputFile := OutputTextFile("Desktop/BC-Blue.txt", false);
	SetPrintFormattingStatus(outputFile, false);
	PrintTo(outputFile); # Make file empty
	
	## In the following, each list has 9 elements, all of which are terms.
	# list0 is a list of 9 indeterminates.
	list0 := List([ "u", "a", "b", "v", "c", "w", "d", "r", "s" ], x -> IndetForString(x));
	
	## "Working halfway down"
	# 1
	listDown := rule3232(list0, 4);
	# 2
	listDown := ruleSwitch(listDown, 7);
	# 3
	listDown := rule212(listDown, 2);
	# 4
	listDown := ruleSwitch(listDown, 1);
	listDown := ruleSwitch(listDown, 4);
	# 5
	listDown := rule121(listDown, 5);
	# 6
	listDown := rule3232(listDown, 2);
	# 7
	listDown := ruleSwitch(listDown, 5);
	# 8
	listDown := rule3232(listDown, 6);
	# 9
	listDown := rule212(listDown, 4);
	# 10
	listDown := ruleSwitch(listDown, 3);
	listDown := ruleSwitch(listDown, 6);
	# 11
	listDown := rule121(listDown, 1);
	
	## "Working halfway up"
	# 23
	listUp := rule212(list0, 7);
	# 22
	listUp := ruleSwitch(listUp, 3);
	listUp := ruleSwitch(listUp, 6);
	# 21
	listUp := rule121(listUp, 4);
	# 20
	listUp := rule3232(listUp, 1);
	# 19
	listUp := ruleSwitch(listUp, 4);
	# 18
	listUp := rule3232(listUp, 5);
	# 17
	listUp := ruleSwitch(listUp, 8);
	# 16
	listUp := rule212(listUp, 3);
	# 15
	listUp := ruleSwitch(listUp, 2);
	listUp := ruleSwitch(listUp, 5);
	# 14
	listUp := rule121(listUp, 6);
	# 13
	listUp := rule3232(listUp, 3);
	
	## Create the main content of a basic LaTeX file which displays the result. Preamble not included.
	for i in [1..9] do
		AppendTo(outputFile, "\\textbf{", i, ". column:}\n\n");
		AppendTo(outputFile, "\\addvspace{0.1cm}\n");
		AppendTo(outputFile, "(1) -- (12): $ ", TermAsString(listDown[i]), " $\n\n");
		AppendTo(outputFile, "(23) -- (12): $ ", TermAsString(listUp[i]), " $");
		if i < 9 then
			AppendTo(outputFile, "\n\n\\addvspace{0.4cm}");
		fi;
	od;
	return [ listDown, listUp];
end;

## Some tests

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

test3232 := function()
	local list0, list1, i;
	list0 := List(["s", "u", "t", "v"], x -> IndetForString(x));
	list1 := rule3232(list0, 1);
	for i in [1..4] do
		Display(TermAsString(list1[i]));
	od;
end;