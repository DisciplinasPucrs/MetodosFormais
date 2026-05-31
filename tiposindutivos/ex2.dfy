datatype Lista<T> = Vazia | Cons(cabeca:T, cauda:Lista<T>)

function Tamanho<T>(lista:Lista<T>):nat
{
  //expressão condicional
  if lista == Vazia
  then 0
  else 1 + Tamanho(lista.cauda)
}

function Tamanhov2<T>(lista:Lista<T>):nat
{
  //casamento de padrões
  match lista
  case Vazia => 0
  case Cons(cabeca,cauda) => 1 + Tamanhov2(cauda)
}

function Concatenar<T>(x:Lista<T>, y:Lista<T>):Lista<T>
  ensures Tamanhov2(Concatenar(x,y)) == Tamanhov2(x) + Tamanhov2(y)
{
  match x
  case Vazia => y
  case Cons(cabeca,cauda) => Cons(cabeca, Concatenar(cauda,y))
}

lemma ConcatenarAssociatividade<T>(x:Lista<T>, y:Lista<T>, z:Lista<T>)
  ensures Concatenar(Concatenar(x,y),z) == Concatenar(x,Concatenar(y,z))
{}

method Main()
{
  var lista1:Lista<int> := Vazia;
  var lista2 := Cons(1,Vazia);
  var lista3 := Cons(1,Cons(2,Vazia));
  assert Tamanhov2(lista1) == 0;
  assert Tamanhov2(lista2) == 1;
  assert Tamanhov2(lista3) == 2;
  var lista4 := Concatenar(lista2, lista3);
  assert Tamanhov2(lista4) == 3;
}
