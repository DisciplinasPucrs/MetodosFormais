ghost predicate Permutacao(a:seq<int>, b:seq<int>) 
{ 
    multiset(a) == multiset(b) 
}

ghost predicate OrdenadoCrescente(s:seq<int>) 
{ 
    forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1] 
}

ghost predicate ParticaoMenorMaior(s:seq<int>, p:int)
  requires 0 <= p <= |s|
{
  forall i,j :: 0 <= i < p <= j < |s| ==> s[i] <= s[j]
}

method BubbleSort(a:array<int>) 
  ensures OrdenadoCrescente(a[..]) 
  ensures Permutacao(a[..], old(a[..])) 
  modifies a
{
    var n := a.Length;
    var i := 0;
    while i < n
    invariant 0 <= i <= n
    invariant OrdenadoCrescente(a[n-i..n])
    invariant Permutacao(a[..], old(a[..]))
    invariant ParticaoMenorMaior(a[..], n-i)
    {
        var j := 0;
        while j < n - i - 1
        invariant 0 <= j <= n-i-1
        invariant forall k :: 0 <= k <= j ==> a[k] <= a[j] //bolha andou para direita
        invariant OrdenadoCrescente(a[n-i..n])
        invariant Permutacao(a[..], old(a[..]))
        invariant ParticaoMenorMaior(a[..], n-i)
        {
            if a[j] > a[j+1]
            {
                a[j], a[j+1] := a[j+1], a[j];
            }
            j := j + 1;
        }
        i := i + 1;
    }
}
