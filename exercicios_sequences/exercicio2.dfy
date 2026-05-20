ghost predicate Ordenado(s: seq<int>)
{
  forall i :: 0 < i < |s| ==> s[0] < s[i] && Ordenado(s[1..])
}

ghost predicate OrdenadoV2(s: seq<int>)
{
  s == [] ||
  s == [s[0]] ||
  (s[0] < s[1] && OrdenadoV2(s[1..]))
}

method Main() {
  var s0 := [];
  assert Ordenado(s0);
  assert OrdenadoV2(s0);
  var s1 := [1];
  assert Ordenado(s1);
  assert OrdenadoV2(s1);
  var s2 := [1, 2, 3, 4, 5];
  assert Ordenado(s2);
  assert OrdenadoV2(s2);
}
