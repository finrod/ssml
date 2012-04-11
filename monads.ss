signature MONAD (m : * -> *) = sig
  val return : 'a -> m 'a
  val bind   : m 'a -> ('a -> m 'b) -> m 'b
end

datatype option : * -> * = Some : 'a -> option 'a | None : option 'a

structure OptionMonad : MONAD option = struct
  fun return x = Some x
  fun bind ox f =
    case ox of
        Some x => f x
      | None => None
    end
end

datatype list : * -> * = Nil : list 'a | Cons : 'a -> list 'a -> list 'a

fun append xs ys =
  case xs of
      Nil => ys
    | Cons x xs => Cons x (append xs ys)
  end

fun concat xss =
  case xss of
      Nil => Nil
    | Cons xs xss => append xs (concat xss)
  end

fun map f xs =
  case xs of
      Nil => Nil
    | Cons x xs => Cons (f x) (map f xs)
  end

structure ListMonad : MONAD list = struct
  fun return x = Cons x Nil
  fun bind xs f = concat (map f xs)
end

datatype bool : * = True : bool | False : bool

signature EQ (t : *) = sig
  val eq : t -> t -> bool
end

structure Bool = struct
  fun and b1 b2 = case b1 of True => b2 | False => False end
  fun or b1 b2 = case b1 of True => True | False => b2 end
  fun neg b = case b of True => False | False => True end
end

structure BoolEq : EQ bool = struct
  fun eq b1 b2 =
    case b1 of True => b2
             | False => Bool.neg b2
    end
end

structure ListEq =
  fn {X : EQ 'a} =>
  struct
    fun eq xs ys =
      case xs of Cons x xs' =>
        case ys of Cons y ys' =>
          Bool.and (X.eq x y) (eq xs' ys')
        | Nil => False
        end
      | Nil =>
        case ys of Nil => True
        | Cons y ys' => False
        end
      end
  end : EQ (list 'a)


fun join {M : MONAD 'm} t = M.bind t (fn x => x)

val blah = join (Cons (Cons True Nil) Nil)

fun find {E : EQ 'a} xs y =
  case xs of
    Cons x xs' =>
    case E.eq x y of
      True => Some x
    | False => find xs' y
    end
  | Nil => None
  end

fun findToList {E : EQ 'a} xs y =
  case find xs y of
    Some x => Cons x Nil
  | None => Nil
  end

val blah2 = find (Cons (Cons True Nil) (Cons (Cons False Nil) Nil)) (Cons True Nil)

