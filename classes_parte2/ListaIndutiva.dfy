datatype list<T> =
  | Nil
  | Cons(hd: T, tl: list)

function tamanho<T>(l: list): nat
{
  match l
  {
    case Nil => 0
    case Cons(h,t) => 1 + tamanho(t)
  }
}

function concatenar<T>(l1: list, l2: list): list
{
  match l1 {
    case Nil => l2
    case Cons(h,t) => Cons(h,concatenar(t,l2))
  }
}

function inverter<T>(l:list):list
{
    inverterAux(l,Nil)
}

function inverterAux<T>(l: list, acc: list): list
{
  match l {
    case Nil => acc
    case Cons(h,t) => inverterAux(t,Cons(h,acc))
  }
}