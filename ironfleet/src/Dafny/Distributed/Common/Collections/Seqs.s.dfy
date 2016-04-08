
module Collections__Seqs_s {

function last<T>(s:seq<T>):T
    requires |s| > 0;
{
    s[|s|-1]
}

function all_but_last<T>(s:seq<T>):seq<T>
    requires |s| > 0;
    ensures  |all_but_last(s)| == |s| - 1;
{
    s[..|s|-1]
}

function middle<T>(s:seq<T>):seq<T>
    requires |s| >= 2;
    ensures  |middle(s)| == |s| - 2;
    ensures  forall i {:trigger middle(s)[i]} :: 0 <= i < |s| - 2 ==> middle(s)[i] == s[i+1];
{
    s[1..|s|-1]
}
    
}
