ghost predicate Permutacao(a:seq<int>, b:seq<int>)
{
  multiset(a) == multiset(b)
}

ghost predicate OrdenadoEntre(a:seq<int>, e:int, d:int)
  requires 0 <= e <= d <= |a|
{
  forall i,j ::e <= i <= j < d ==> a[i] <= a[j]
}

ghost predicate Ordenado(a:seq<int>)
{
  OrdenadoEntre(a,0,|a|)
}

method BubbleSort(a:array<int>)
  modifies a
  ensures Ordenado(a[..])
  ensures Permutacao(a[..], old(a[..]))
{
  if a.Length > 1
  {
    var i := 1;
    while i < a.Length
      invariant 1 <= i <= a.Length
      invariant OrdenadoEntre(a[..],0,i)
      invariant Permutacao(a[..], old(a[..]))
    {
      BubbleStep(a,i);
      i := i + 1;
    }
  }
}

method BubbleStep(a:array<int>, i:int)
  requires 0 <= i < a.Length
  requires OrdenadoEntre(a[..],0,i)
  modifies a
  ensures OrdenadoEntre(a[..],0,i+1)
  ensures Permutacao(a[..], old(a[..]))
{
  var j := i;
  while j > 0 && a[j-1] > a[j]
    invariant 0 <= j <= i
    invariant OrdenadoEntre(a[..],0,j) && OrdenadoEntre(a[..],j,i+1)
    invariant 1 < j+1 <= i ==> a[j-1] <= a[j+1]
    invariant Permutacao(a[..], old(a[..]))
  {
    a[j-1], a[j] := a[j], a[j-1];
    j := j - 1;
  }
}

method Main()
{
  var a := new int[4];
  a[0], a[1], a[2], a[3] := 10, 1, 0, 5;
  assert a[..] == [10,1,0,5];
  BubbleSort(a);
  assert a[..] == [0,1,5,10];
}
