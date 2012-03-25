structure Examples =
struct

    val Sum.INR example1 = SSParse.parseDef "fun id x = x"
        (*= Ast.ValRecBind (a, NONE, 
            Ast.Fn (Ast.Expl (x, NONE), Ast.Var (x, NONE), NONE))*)

    val Sum.INR example2 = SSParse.parseDef "val a = fn x => x x"
      (*= Ast.ValBind (a, NONE, Ast.Fn (Ast.Expl (x, NONE), Ast.App (Ast.Var (x, NONE), Ast.Var (x, NONE), NONE), NONE))*)

    val Sum.INR example3 = SSParse.parseExp "let val id = fn x => x in id id end"
      (*= Ast.Let ([Ast.ValBind (a, NONE, Ast.Fn (Ast.Expl (x, NONE), Ast.Var (x, NONE), NONE))],
		 Ast.App (Ast.Var (a, NONE), Ast.Var (a, NONE), NONE), NONE)*)

    val Sum.INR example4 = SSParse.parseDef "fun loop x = loop x"
      (*= Ast.ValRecBind (a, NONE, Ast.Fn (Ast.Expl (x, NONE), Ast.App (Ast.Var (a, NONE), Ast.Var (x, NONE), NONE), NONE))*)

    val Sum.INR monadDecl = SSParse.parseDef "signature MONAD (m : * -> *) = sig\n  val return : 'a -> m 'a\n  val bind : m 'a -> ('a -> m 'b) -> m 'b\nend"
    (*  = Ast.SigDec (monad, SOME (t, Ast.KArr (Ast.KTy, Ast.KTy)), Ast.TySig
				[Ast.ValDec (return, Ast.TyArrow (Ast.TyPoly x, Ast.TyApp (Ast.TyId t, Ast.TyPoly x))),
				 Ast.ValDec (bind, Ast.TyArrow (Ast.TyApp (Ast.TyId t, Ast.TyPoly a), Ast.TyArrow (Ast.TyArrow (Ast.TyPoly a, Ast.TyApp (Ast.TyId t, Ast.TyPoly x)), Ast.TyApp (Ast.TyId t, Ast.TyPoly x))))])

    val monadType = Ast.TyLam (t, Ast.KArr (Ast.KTy, Ast.KTy), Ast.TySig
				[Ast.ValDec (return, Ast.TyArrow (Ast.TyPoly x, Ast.TyApp (Ast.TyId t, Ast.TyPoly x))),
				 Ast.ValDec (bind, Ast.TyArrow (Ast.TyApp (Ast.TyId t, Ast.TyPoly a), Ast.TyArrow (Ast.TyArrow (Ast.TyPoly a, Ast.TyApp (Ast.TyId t, Ast.TyPoly x)), Ast.TyApp (Ast.TyId t, Ast.TyPoly x))))])*)

(*    fun run' e =
        let
            val s = HM.reset ()
            val e' = HM.constrDec e
        in
            (print "===========================================\n";
             print ("Pre-constr: " ^ (Ast.ppdec e) ^ "\n");
             HM.constrDec e;
             print ((HM.printConstr ()) ^ "\n");
             print ("Post-constr: " ^ (Ast.ppdec e') ^ "\n");
	     print (HM.printConstr' (HM.unify (!HM.constraints)) ^ "\n");
	     print ("Post-uni: " ^ (Ast.ppdec e') ^ "\n");
             print "===========================================\n";
             ())
         end

    fun run () = 
        (run' example1;
         ())*)
end


