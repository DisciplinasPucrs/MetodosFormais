//Observe a ordem que os elementos são processados no unfold da recursão
//entre Somatorio e SomatorioR
ghost function Somatorio(xs: seq<int>): int
{
  if xs == []
  then 0
  else xs[0] + Somatorio(xs[1..])
}

//Observe a ordem que os elementos são processados no unfold da recursão
//entre Somatorio e SomatorioR
ghost function SomatorioR(xs: seq<int>): int
{
  if xs == []
  then 0
  else xs[|xs|-1] + SomatorioR(xs[..|xs|-1])
}

//Essa versão consegue provar
//A ordem que o array é percorrido está de acordo com o unfold da recursão

method SomarDirEsq(a: array<int>) returns (s: int)
ensures s == Somatorio(a[..])
{
  s := 0;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant s == Somatorio(a[a.Length-i..])
  {
    s := s + a[a.Length - i-1];
    i := i + 1;
  }
}

method SomarDirEsqV2(a: array<int>) returns (s: int)
ensures s == Somatorio(a[..])
{
  s := 0;
  var i := a.Length;
  while i > 0
    invariant 0 <= i <= a.Length
    invariant s == Somatorio(a[i..])
  {
    i := i - 1;
    s := s + a[i];
  }
}

//Essa versão não consegue provar
//A ordem que o array é percorrido NÃO está de acordo com o unfold da recursão
/*
method SomarEsqDir(a: array<int>) returns (s: int)
ensures s == Somatorio(a[..])
{
    s := 0;
    var i := 0;
    while i < a.Length
    invariant 0 <= i <= a.Length
    invariant s == Somatorio(a[..i])
    {
        s := s + a[i];
        i := i + 1;
    }
}
*/

//Essa versão não consegue provar sem as duas asserções adicionais no código
//A última asserção é necessária pois a poscondição usa a[..] mas o laço de repetição
//usa a[..i], então precisamos forçar o Dafny a provar a igualdade
//A asserção no início do laço de repetição é necessária pois a invariante usa a[..i]
//então precisamos forçar o Dafny a provar a igualdade que falta devido à forma
//como o processo de dedução ocorre na lógica de Hoare
/*
method SomarEsqDir(a: array<int>) returns (s: int)
ensures s == SomatorioR(a[..])
{
    s := 0;
    var i := 0;
    while i < a.Length
    invariant 0 <= i <= a.Length
    invariant s == SomatorioR(a[..i])
    {
        assert a[..i+1][..i] == a[..i];
        s := s + a[i];
        i := i + 1;
    }
    assert a[..i] == a[..];
}
*/


//Versão alternativa

ghost function SomatorioAte(xs: seq<int>, n:int): int
requires 0 <= n <= |xs|
{
  if n == 0
  then 0
  else SomatorioAte(xs, n-1) + xs[n-1]
}

method SomarV2(a: array<int>) returns (s: int)
ensures s == SomatorioAte(a[..], a.Length)
{
  s := 0;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant s == SomatorioAte(a[..], i)
  {
    s := s + a[i];
    i := i + 1;
  }
}

method Main()
{
  var a := new int[3];
  a[0], a[1], a[2] := 1,2,3;
  var s := SomarDirEsq(a);
  assert s == Somatorio(a[..]);
}
