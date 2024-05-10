abstract module Expression{
    type Name = nat

    datatype Exp = Var (Name)
                 | Not (Exp) 
                 | And (Exp, Exp) 
                 | Implies (Exp, Exp)
    
    function subst (n : Name, e1 : Exp, e2 : Exp) : Exp
}

abstract module VCG {
import opened Expression

datatype Program = Assign (Name, Exp)
                 | Seq (Program, Program)
                 | If (Exp, Program, Program)
                 | While (inv : Exp, guard : Exp, body : Program)

type Triplet = (Exp, Program, Exp)
type Conds = multiset<Exp>

datatype Hoare = Assign (Name, Exp, post : Exp)
               | Seq (Hoare, Hoare)
               | If (Exp, Hoare, Hoare)
               | While (Exp, Hoare)
               | Conseq (Hoare, Exp, Exp)

datatype Chk = Ok (Triplet, Conds)
             | Fail

function chk (h : Hoare) : Chk
{
    match h
        case Assign (x, e, post) => Ok ((subst (x, e, post), Program.Assign (x, e), post), multiset{})
        case Seq (h1, h2) => (match chk (h1)
                                case Ok ((pre, p1, p), cs1) => (match chk (h2)
                                                                case Ok ((p', p2, post), cs2) =>
                                                                     if p == p' then Ok ((pre, Program.Seq (p1, p2), post), cs1 + cs2)
                                                                     else Fail 
                                                                case Fail => Fail)
                                case Fail => Fail)
        case If (b, ht, he) => (match chk (ht)
                                  case Ok ((And (bt, pret), pt, postt), cst) => (match chk (he)
                                                                                case Ok ((And (be, pree), pe, poste), cse) =>
                                                                                    if bt == b && be == Not (b) && pret == pree && postt == poste 
                                                                                    then Ok ((pret, Program.If (b, pt, pe), postt), cst + cse)
                                                                                     else Fail 
                                                                                case Ok ((Var(_), _, _), _) => Fail
                                                                                case Ok ((Not(_), _, _), _) => Fail
                                                                                case Ok ((Implies(_, _), _, _), _) => Fail                                                                                    
                                                                                case Fail => Fail)
                                  case Ok ((Var(_), _, _), _) => Fail
                                  case Ok ((Not(_), _, _), _) => Fail
                                  case Ok ((Implies(_, _), _, _), _) => Fail
                                  case Fail => Fail)
        case While (b, hs) => (match chk (hs)
                                case Ok ((And (bs, pres), ps, posts), css) => if bs == b && pres == posts
                                                                              then Ok ((pres, Program.While (pres, b, ps), And(Not(b), pres)), css) 
                                                                              else Fail
                                case Ok ((Var(_), _, _), _) => Fail
                                case Ok ((Not(_), _, _), _) => Fail
                                case Ok ((Implies(_, _), _, _), _) => Fail
                                case Fail => Fail)
        case Conseq (hp, pre, post) => match chk (hp)
                                         case Ok ((prep, p, postp), cs) => Ok ((pre, p, post), cs + multiset{Implies (pre, prep), Implies (postp, post)})
                                         case Fail => Fail
}

function vcg (t : Triplet) : (Hoare, Conds)
ensures var (h, cs) := vcg (t) ; chk (h) == Ok (t, cs)





}