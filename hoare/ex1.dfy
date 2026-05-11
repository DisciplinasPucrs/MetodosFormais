method Exemplo(y:nat) returns (x:nat)
  requires y <= 4
  ensures x <= 5
{
    assert y + 1 <= 5; //obtido pelo cálculo da precondição mais fraca via Floyd-Hoare
    x := y + 1;
    assert x <= 5;
}

// A condição de verificação para a correção é:
// y <= 4 ==> y + 1 <= 5
