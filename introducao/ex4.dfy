ghost function Fat(n: nat): nat
  decreases n
//A verificação depende da implementação concreta; diz-se que funções são transparentes
{
   if n == 0 then 1 else n * Fat(n-1)
}

method Fatorial(n:nat)  returns (r:nat)
  ensures r == Fat(n)
{
    r := 1;
    var i := 0;
    while i < n
      decreases n-i
      invariant r == Fat(i) && i <= n
    {
        i := i + 1;
        r := r * i;
    }
}
