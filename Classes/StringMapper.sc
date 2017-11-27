/*
StringMapper creates mappings between elements shared by source and target collections according to selectable rules.
The mapping is represented as an array of triples: [element, sourceIndex, targetIndex]
targetIndex is nil for unmapped elements in the source
sourceIndex is nil for unmapped elements in the target

diffFunc: a function that takes source and target collections as arguments and returns a mapping

MapString::diff(target, source(optional) ) maps from the previous target (or the source argument, if provided) to the target.

preprocess: strips off a prefix delimited with "/" and sends it as a message to the StringMapper
*/

StringMapper {
	var <>prevTokens;
	var <>diffFunc;

	*new { |insertFunc, removeFunc, keepFunc, beginFunc, returnFunc, testFunc|
		^super.newCopyArgs(insertFunc, removeFunc, keepFunc, beginFunc, returnFunc, testFunc ? true).init
	}

	init { prevTokens = ""; this.diff0; }

	diff { |  target, source  |
		var mapping;
		target = this.preprocess(target);
		mapping = diffFunc.value(source ? prevTokens, target);
		prevTokens = target;
		^mapping;
	}

	preprocess { | tokens |
		var diffSelector, tokenList;
		if (tokens.includes($/)) {
			tokenList = tokens.postln.split($/);
			tokens = tokenList.last;
			diffSelector = tokenList.first;
			this.perform(diffSelector.asSymbol);
		};
		^tokens;
	}
	// levenshtein distance,
	// takes source and target collections, and
	// returns a matrix which determines the minimum
	// number of deletions and insertions needed to convert the source to the target
	// and can be used to create the appropriate sequence of substitutions

	ld { | s,t|
		var m,n, d, cost;
		m = s.size;
		n = t.size;
		d = m.collect {| i |  0.dup(n).addFirst(i + 1) };
		d = d.addFirst( (0..n) );
		n.do { | j |
			j = j + 1;
			m.do { | i |
				i = i + 1;
				if (s[i-1] == t[j-1]) {
					cost = 0
				} {
					cost = 1;
				};
				d[i][j] = (d[i-1][j] + 1) 				// deletion
				min: (d[i][j-1] + 1) 					// insertion
				min: (d[i-1][j-1] + cost);				// substitution

			}
		};
		^d;
	}

	parseld { | table, s, t |
		var changes;  // array of [token, sourceIndex | nil, targetIndex | nil]
		var sourceIndex = table.size - 1;		// sourceIndex
		var targetIndex = table[0].size - 1;	// targetIndex

		changes = Array(s.size  + t.size + 1);
		while{ (sourceIndex >0) && (targetIndex >0) } {
			// hack in a preference for contiguous characters
			// so txtest -> test takes txTEST rather than TxtEST
			if (s[sourceIndex-1] == t[targetIndex-1]) {
				sourceIndex = sourceIndex -1; targetIndex = targetIndex-1;
				changes.add([s[sourceIndex], sourceIndex, targetIndex]);
			} {
				if (table[sourceIndex -1][targetIndex] <= table[sourceIndex][targetIndex-1])
				{ sourceIndex = sourceIndex -1; changes.add([s[sourceIndex], sourceIndex, nil]);}
				{ targetIndex = targetIndex-1; changes.add([t[targetIndex], nil, targetIndex])};
			};
		};
		// now get the leftovers, which will be either in the source or the target
		sourceIndex.reverseDo{ | sourceIndex | changes.add([s[sourceIndex], sourceIndex, nil]);};
		targetIndex.reverseDo{| targetIndex | changes.add([t[targetIndex], nil, targetIndex])};
		^changes.reverse;
	}

	// display the Levenshtein matrix
	study { |s, t|
		var matrix= this.ld(s, t);
		matrix = matrix.collect({| l, i | l.addFirst((" " ++ s)[i]) });
		matrix = matrix.addFirst(("  " ++ t).collectAs({|x| x}, Array));
		^matrix
	}

	makeStringOfMapping { | mapping |
		var s, t, char, si, ti;
		s = String.new;
		t = String.new;
		mapping.do({ | triple |
			#char, si, ti = triple;
			if (si.notNil && ti.notNil) { char = char.toUpper };
			if (si.notNil) { s = s.add(char) };
			if (ti.notNil) { t = t.add(char) };
		});
		^[t, s]
	}


	// basic levenstein solution tends to retain elements towards the end of the target
	diff0 {
		diffFunc = {| prevTokens, tokens |
			this.parseld(this.ld(prevTokens, tokens), prevTokens, tokens);
		}
	}

	// here collections are reversed to retain elements towards the beginning of the target
	diff1 {
		diffFunc = {| prevTokens, tokens |
			var changes, psz, tsz, reversedChanges;
			psz = prevTokens.size - 1;
			tsz = tokens.size - 1;
			prevTokens = prevTokens.reverse;
			tokens = tokens.reverse;
			changes = this.parseld(this.ld(prevTokens, tokens), prevTokens, tokens);
			changes = changes.collect { | tst |	//token, source, target
				tst[1] !? { tst[1] = psz - tst[1]};
				tst[2] !? { tst[2] = tsz - tst[2]};
				tst;
			};
			changes.reverse;
		}
	}

	// shared elements are mapped by their order positions, so
	//  aabc -> abc removes the second "a" from the source
	// abc -> aaabc maps "a" in the source to the first "a" in the target
	diff2 {
		diffFunc = {| prevTokens, tokens |
			var d, n, prevPos = ();
			prevTokens.do{ | c, i |
				prevPos[c] = prevPos[c].add(i)
			};
			tokens.do { | c, i |
				n = n.add([c, prevPos[c].pop, i])
			};
			prevPos.keysValuesDo{ |k, v | if (v.size >0) {d = d ++ [k,v, nil].flop } };
			d ++ n;
		}
	}

	// shared elements are mapped by inverting order positions, so
	//  later elements in the source go to later elements in the target
	diff3 {
		diffFunc = {| prevTokens, tokens |
			var sz, d, n, prevPos = ();
			prevTokens.reverseDo{ | c, i |
				prevPos[c] = prevPos[c].add(i)
			};
			tokens.do { | c, i |
				n = n.add([c, prevPos[c].pop, i])
			};
			n = n.reverse;
			prevPos.keysValuesDo{ |k, v | if (v.size >0) {d = d ++ [k,v, nil].flop } };
			d ++ n;
		}
	}
}

/*
a = StringMapper();
a.diff0.makeStringOfMapping(a.diff( "ababa", "aaabaaab") ).postln;
a.diff1.makeStringOfMapping(a.diff( "ababa", "aaabaaab") ).postln;
a.diff2.makeStringOfMapping(a.diff( "ababa", "aaabaaab") ).postln;
a.diff3.makeStringOfMapping(a.diff( "ababa", "aaabaaab") ).postln;

a.diff0.makeStringOfMapping(a.diff("aab", "accdaabq") ).postln;
a.diff1.makeStringOfMapping(a.diff("aab", "accdaabq") ).postln;
a.diff2.makeStringOfMapping(a.diff("aab", "accdaabq") ).postln;
a.diff3.makeStringOfMapping(a.diff("aab", "accdaabq") ).postln;

*/