use "Set.sml";
signature FORM = sig
	datatype form =
		Absurdum | propSymb of string | Negation of form |
		Conjunction of form*form | Disjunction of form*form |
		Implication of form*form
	exception SyntaxError of string
	val getpropSymbs : form -> string Set.myset
	val parse : string -> form
	val format : form -> string
end
structure Form :> FORM = struct
	datatype token =
		LogicalAbsurdum | Literal of char | LogicalNot |
		LogicalAnd | LogicalOr | LogicalImplies | LParen | RParen
	exception LexicalError
	fun tokenize [] = []
		| tokenize ( #"-" :: #">" :: cs) = (LogicalImplies :: tokenize(cs))
		| tokenize ( #"-" :: c :: cs) = raise LexicalError
		| tokenize ( #"&" :: #"&" :: cs) = (LogicalAnd :: tokenize(cs))
		| tokenize ( #"&" :: c :: cs) = raise LexicalError
		| tokenize ( #"|" :: #"|" :: cs) = (LogicalOr :: tokenize(cs))
		| tokenize ( #"|" :: c :: cs) = raise LexicalError
		| tokenize ( #"!" :: cs) = (LogicalNot :: tokenize(cs))
		| tokenize ( #"_" :: cs) = (LogicalAbsurdum :: tokenize(cs))
		| tokenize ( #"(" :: cs) = (LParen :: tokenize(cs))
		| tokenize ( #")" :: cs) = (RParen :: tokenize(cs))
		| tokenize (c :: cs) = Literal c :: tokenize(cs)
	datatype form =
		Absurdum | propSymb of string | Negation of form |
		Conjunction of form*form | Disjunction of form*form |
		Implication of form*form
	exception SyntaxError of string
	fun getpropSymbs Absurdum = []
		| getpropSymbs (propSymb c) = [c]
		| getpropSymbs (Negation A) = getpropSymbs(A)
		| getpropSymbs (Conjunction(A,B)) = Set.union(getpropSymbs(A),getpropSymbs(B))
		| getpropSymbs (Disjunction(A,B)) = Set.union(getpropSymbs(A),getpropSymbs(B))
		| getpropSymbs (Implication(A,B)) = Set.union(getpropSymbs(A),getpropSymbs(B))
	fun parse_imp fm = 
		let
			val ( f , fm') = parse_or fm
		in
			case fm'
				of (LogicalImplies :: fm'') =>
					let
						val ( f' , fm''') = parse_imp fm''
					in
						(Implication ( f , f') , fm''')
					end
				| _ => (f, fm')
		end
	and parse_or fm = 
		let
			val ( f , fm') = parse_and fm
		in
			case fm'
				of (LogicalOr :: fm'') =>
					let
						val ( f' , fm''') = parse_or fm''
					in
						(Disjunction ( f , f') , fm''')
					end
				| _ => (f, fm')
		end
	and parse_and fm = 
		let
			val ( f , fm') = parse_atom fm
		in
			case fm'
				of (LogicalAnd :: fm'') =>
					let
						val ( f' , fm''') = parse_and fm''
					in
						(Conjunction ( f , f') , fm''')
					end
				| _ => (f, fm')
		end
	and parse_atom nil = raise SyntaxError ("Factor Expected \n")
		| parse_atom (LogicalNot :: fm) = 
			let
				val ( f , fm') = parse_atom fm
			in
				(Negation f , fm')
			end
		| parse_atom ((Literal f) :: fm) = 
			let
				fun charlstfrmtokens((Literal x)::xs) = x::charlstfrmtokens(xs)
					| charlstfrmtokens(x) = []
				fun rempart((Literal x)::xs) = rempart(xs)
					| rempart(x)=x
			in (propSymb(String.implode(charlstfrmtokens((Literal f)::fm))),rempart((Literal f)::fm))
			end
		| parse_atom (LogicalAbsurdum :: fm) = (Absurdum , fm)
		| parse_atom (Lparen :: fm) =
			let
				val ( f , fm') = parse_imp fm
			in
				case fm'
					of nil => raise SyntaxError ("Right Parenthesis Expected .\n")
					| (RParen :: fm'') => ( f , fm'')
					| _ => raise SyntaxError ("Right Parenthesis Expected .\n")
			end
	fun parse s =
		let
			val ( f , fm) = parse_imp (tokenize (String.explode s))
		in
			case fm
				of nil => f
				| _ => raise SyntaxError ("Unexpected Input .\n")
		end
		handle LexicalError => raise SyntaxError ("Invalid Input .\n")
	fun format_exp Absurdum = [#"_"]
		| format_exp (propSymb P) = String.explode(P)
		| format_exp (Negation A) = 
			let
				val s = format_exp A
			in ([#"("] @ [#"!"] @ s @ [#")"])
			end
		| format_exp (Conjunction (A,B)) = 
			let
				val n = format_exp A
				val n' = format_exp B
			in [#"("] @ n @ [#"&"] @ [#"&"] @ n' @ [#")"]
			end
		| format_exp (Disjunction (A,B)) = 
			let
				val n = format_exp A
				val n' = format_exp B
			in ([#"("] @ n @ [#"|"] @ [#"|"] @ n' @ [#")"])
			end
		| format_exp (Implication (A,B)) = 
			let
				val n = format_exp A
				val n' = format_exp B
			in ([#"("] @ n @ [#"-"] @ [#">"] @ n' @ [#")"])
			end
	fun format f = String.implode (format_exp f)
end;
