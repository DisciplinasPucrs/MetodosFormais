ghost predicate Permutacao(a:seq<int>, b:seq<int>)
{
  multiset(a) == multiset(b)
}

method Main()
{
  var a := new nat[3];
  a[0], a[1], a[2] := 1, 2, 3;
  var b := new nat[3];
  b[0], b[1], b[2] := 3, 1, 2;
  assert a[..] == [1,2,3] && b[..] == [3,1,2]; //asserção necessária para o verificador conhecer o conteúdo do array
  assert Permutacao(a[..], b[..]);
}
