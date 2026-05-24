method TrocaElementos(a: array<int>, i: int, j: int)
  //precondição para índices válidos no array
  requires 0 <= i < j < a.Length
  //frame de escrita para indicar alteração no array
  modifies a
  //poscondição para indicar que a quantidade de cada elemento do array não mudou
  //ensures multiset(old(a[..])) == multiset(a[..])
  //poscondição para indicar a mudança de posição entre i e j
  ensures a[j] == old(a[i]) && a[i] == old(a[j])
  //poscondição para indicar que as demais posições permanecem as mesmas
  ensures forall k :: 0 <= k < a.Length && k !in {i, j} ==> a[k] == old(a[k])
{
  a[i], a[j] := a[j], a[i];
}

method Main()
{
  /*
  var a := new int[3];
  a[0], a[1], a[2] := 1, 2, 3;
  ghost var antes := a;
  TrocaElementos(a,0,2);
  assert multiset(antes[..]) == multiset(a[..]);
  assert a[0] == 3;
  assert a[1] == 2;
  assert a[2] == 1;
  */
  var a := new int[] [1,2,3,4,5];
  assert a[..] == [1,2,3,4,5];
  TrocaElementos(a,0,3);
  assert a[..] == [4,2,3,1,5];
}
