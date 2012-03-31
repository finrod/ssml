structure Reserved :> MINI_LANGUAGE_DEF =
struct

  val reservedNames = ["val", "fun", "type", "rec", "let", "in", "end", "fn",
		       "signature", "sig", "structure", "struct", "datatype",
		       "case", "of", "int", "if", "then", "else"]
  val reservedOpNames = ["=>", ":", "=", "->", "|"]

end

structure SSParse =
struct

  structure LD = MLStyle (Reserved)
  structure TP = TokenParser (LD)
  open Sum

  open ParserCombinators
  open CharParser
  infixr 4 << >>
  infixr 3 &&
  infix  2 -- ##
  infix  2 wth suchthat return guard when
  infixr 1 || <|> ??

  val cntr = ref 0
  val polyMap : (Ast.name * Ast.id) list ref = ref []
  fun getPoly n =
      (case List.find (fn (x, _) => x = n) (!polyMap) of
	   SOME (_, i) => i
	 | NONE => let val i = !cntr
		   in i before (cntr := i+1; polyMap := (n, i) :: !polyMap) end)


  fun notIn lst x = List.all (fn y => y <> x) lst

  (* helper: get identifier or a longname *)
  val idOrLongName =
      let val name = LD.identStart && repeat LD.identLetter
				   wth implode o op:: suchthat (notIn LD.reservedNames)
      in try (TP.lexeme (separate1 name (CharParser.char #".")))
      end

  val ident = idOrLongName -- (fn [s] => succeed s
				| _ => fail "" ?? "identifier")

  fun iolSplit [] = raise Fail "Impossible happened!"
    | iolSplit [s] = ([], s)
    | iolSplit (s :: ss) = let val (fs, n) = iolSplit ss in (s :: fs, n) end

  fun tyOfIol [s] = Ast.TyId s
    | tyOfIol ss  =
      let val (ss, f) = iolSplit ss
      in Ast.TyLongName (ss, f)
      end

  fun expOfIol [s] = Ast.Var (s, NONE)
    | expOfIol ss  =
      let val (ss, f) = iolSplit ss
      in Ast.LongName (ss, f, NONE)
      end

  (* kind annotations *)
  fun atKnd () = (TP.operator -- (fn "*" => succeed Ast.KTy | _ => fail "" ?? "kind")) <|> TP.parens ($ tKind)
  and tKind () = chainr1 ($ atKnd) (TP.reservedOp "->" return Ast.KArr)

  val kind = $ tKind

  (* types *)
  val tyIdorLN = idOrLongName wth tyOfIol
  val poly = CharParser.char #"'" >> ident wth Ast.TyPoly o getPoly

  fun arTy () = chainr1 ($apTy) (TP.reservedOp "->" return Ast.TyArrow)
  and apTy () = chainl1 ($atTy) (succeed Ast.TyApp)
  and atTy () = tyIdorLN <|> poly <|> TP.parens ($ arTy)
	    <|> TP.reserved "int" return Ast.TyInt
  val typeP = $arTy

  (* function arguments *)
  val tyann = TP.reservedOp ":" >> typeP
  val kindann = TP.reservedOp ":" >> kind

  val args = TP.braces (ident && tyann) wth Ast.Impl
         <|> TP.parens (ident && opt tyann) wth Ast.Expl
	 <|> ident wth (fn x => Ast.Expl (x, NONE))

  (* datatypes (just insides, w/o the constructor) *)
  val data = TP.reserved "datatype" >> ident && kindann << TP.reservedOp "="
	  && separate (ident && tyann) (TP.reservedOp "|") wth flat3

  (* declarations (what goes inside a sig) *)
  val dec = TP.reserved "val"  >> ident && tyann wth Ast.DValDec
	<|> TP.reserved "type" >> ident &&
	    (kindann wth Sum.INL <|> TP.reservedOp "=" >> typeP wth Sum.INR)
	    wth (fn (i, Sum.INL k) => Ast.DTyDec (i, k)
		  | (i, Sum.INR t) => Ast.DTyDef (i, t, NONE))
        <|> data wth Ast.DData
	 ?? "declaration"

  (* patterns (for now very simple) *)
  val pat = ident && repeat ident

  fun tdef () = TP.reserved "val" >> (opt (TP.reserved "rec") wth Option.isSome) &&
	        ident && TP.reservedOp "=" >> $bExp
		wth (fn (true,  (i, e)) => Ast.ValRecBind (i, NONE, e)
		      | (false, (i, e)) => Ast.ValBind (i, NONE, e))
	    <|> TP.reserved "structure" >> ident && opt tyann && TP.reservedOp "=" >> $bExp
		wth (fn (i, (ot, d)) => Ast.StructDec (i, d, ot))
	    <|> TP.reserved "type" >> ident && TP.reservedOp "=" >> typeP
		wth (fn (i, t) => Ast.TyDef (i, t, NONE))
	    <|> data wth Ast.Data
	    <|> TP.reserved "fun" >> ident && repeat1 args && TP.reservedOp "=" >> $bExp
		wth (fn (i, (ars, e)) =>
			Ast.ValRecBind (i, NONE, List.foldr (fn (a, e) => Ast.Fn (a, e, NONE)) e ars))
	    <|> TP.reserved "signature" >> ident && opt (TP.parens (ident && TP.reservedOp ":" >> kind))
		&& TP.reservedOp "=" >> TP.reserved "sig" >> repeat dec << TP.reserved "end"
		wth (fn (i, (SOME (p, k), ds)) => Ast.SigDec (i, SOME (p, k), Ast.TySig ds)
		      | (i, (NONE, ds)) => Ast.SigDec (i, NONE, Ast.TySig ds))

  and bExp () = TP.reserved "fn" >> args && TP.reservedOp "=>" >> $bExp
	        wth (fn (x, y) => Ast.Fn (x, y, NONE))
 	    <|> TP.reserved "let" >> repeat1 ($tdef) && TP.reserved "in" >> $bExp << TP.reserved "end"
	        wth (fn (xs, y) => Ast.Let (xs, y, NONE))
	    <|> TP.reserved "case" >> $bExp << TP.reserved "of" &&
	        separate (pat && TP.reservedOp "=>" >> $bExp) (TP.reservedOp "|") << TP.reserved "end"
		wth (fn (e, cs) => Ast.Case (e, cs, NONE))
	    <|> $anExp
  and anExp () = $apExp && opt tyann wth (fn (e, SOME t) => Ast.Ann (e, t)
					   | (e, NONE) => e)
  and apExp () = chainl1 ($atExp) (succeed (fn (e1, e2) => Ast.App (e1, e2, NONE)))
  and atExp () = idOrLongName wth expOfIol <|> TP.integer wth Ast.VInt
     	     <|> TP.reserved "struct" >> repeat1 ($tdef) << TP.reserved "end"
	     wth (fn ds => Ast.Struct (ds, NONE)) <|> TP.parens ($bExp)

  val exp = $bExp
  val def = $tdef
  val deflist = repeat def

  val parseExp = CharParser.parseString exp
  val parseDef = CharParser.parseString def
  val parseDefList = CharParser.parseString deflist

  fun parseFile fileName =
      let fun isEol s = (case Stream.front s of Stream.Cons (#"\n", _) => true | _ => false)
	  val is = Stream.fromTextInstream (TextIO.openIn fileName)
	  val cs = CoordinatedStream.coordinate isEol (Coord.init fileName) is
      in CharParser.parseChars (deflist << eos) cs
      end

end
