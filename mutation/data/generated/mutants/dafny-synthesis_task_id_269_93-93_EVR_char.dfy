// dafny-synthesis_task_id_269.dfy

method AsciiValue(c: char) returns (ascii: int)
  ensures ascii == c as int
  decreases c
{
  ascii := '0' as int;
}
