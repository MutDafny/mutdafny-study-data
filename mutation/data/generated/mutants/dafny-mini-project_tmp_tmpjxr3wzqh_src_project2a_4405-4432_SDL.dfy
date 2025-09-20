// dafny-mini-project_tmp_tmpjxr3wzqh_src_project2a.dfy

function rem<T(==)>(x: T, s: seq<T>): seq<T>
  ensures x !in rem(x, s)
  ensures forall i: int {:trigger rem(x, s)[i]} :: 0 <= i < |rem(x, s)| ==> rem(x, s)[i] in s
  ensures forall i: int {:trigger s[i]} :: 0 <= i < |s| && s[i] != x ==> s[i] in rem(x, s)
  decreases s
{
  if |s| == 0 then
    []
  else if s[0] == x then
    rem(x, s[1..])
  else
    [s[0]] + rem(x, s[1..])
}

class Address {
  constructor ()
  {
  }
}

class Date {
  constructor ()
  {
  }
}

class MessageId {
  constructor ()
  {
  }
}

class Message {
  var id: MessageId
  var content: string
  var date: Date
  var sender: Address
  var recipients: seq<Address>

  constructor (s: Address)
    ensures fresh(id)
    ensures fresh(date)
    ensures content == ""
    ensures sender == s
    ensures recipients == []
    decreases s
  {
    id := new MessageId();
    date := new Date();
    this.content := "";
    this.sender := s;
    this.recipients := [];
  }

  method setContent(c: string)
    modifies this
    ensures content == c
    decreases c
  {
    this.content := c;
  }

  method setDate(d: Date)
    modifies this
    ensures date == d
    decreases d
  {
    this.date := d;
  }

  method addRecipient(p: nat, r: Address)
    requires p < |recipients|
    modifies this
    ensures |recipients| == |old(recipients)| + 1
    ensures recipients[p] == r
    ensures forall i: int {:trigger old(recipients[i])} {:trigger recipients[i]} :: 0 <= i < p ==> recipients[i] == old(recipients[i])
    ensures forall i: int {:trigger recipients[i]} :: p < i < |recipients| ==> recipients[i] == old(recipients[i - 1])
    decreases p, r
  {
    this.recipients := this.recipients[..p] + [r] + this.recipients[p..];
  }
}

class Mailbox {
  var messages: set<Message>
  var name: string

  constructor (n: string)
    ensures name == n
    ensures messages == {}
    decreases n
  {
    name := n;
    messages := {};
  }

  method add(m: Message)
    modifies this
    ensures m in messages
    ensures messages == old(messages) + {m}
    decreases m
  {
    messages := {m} + messages;
  }

  method remove(m: Message)
    requires m in messages
    modifies this
    ensures m !in messages
    ensures messages == old(messages) - {m}
    decreases m
  {
    messages := messages - {m};
  }

  method empty()
    modifies this
    ensures messages == {}
  {
    messages := {};
  }
}

class MailApp {
  ghost var userboxes: set<Mailbox>
  var inbox: Mailbox
  var drafts: Mailbox
  var trash: Mailbox
  var sent: Mailbox
  var userboxList: seq<Mailbox>

  ghost predicate Valid()
    reads this
    decreases {this}
  {
    inbox != drafts &&
    inbox != trash &&
    inbox != sent &&
    drafts != trash &&
    drafts != sent &&
    inbox !in userboxList &&
    drafts !in userboxList &&
    trash !in userboxList &&
    sent !in userboxList &&
    forall i: int {:trigger userboxList[i]} :: 
      0 <= i < |userboxList| ==>
        userboxList[i] in userboxes
  }

  constructor ()
  {
    inbox := new Mailbox("Inbox");
    drafts := new Mailbox("Drafts");
    trash := new Mailbox("Trash");
    userboxList := [];
  }

  method deleteMailbox(mb: Mailbox)
    requires Valid()
    requires mb in userboxList
    decreases mb
  {
  }

  method newMailbox(n: string)
    requires Valid()
    requires !exists mb: Mailbox {:trigger mb.name} {:trigger mb in userboxList} | mb in userboxList :: mb.name == n
    modifies this
    ensures exists mb: Mailbox {:trigger mb.name} {:trigger mb in userboxList} | mb in userboxList :: mb.name == n
    decreases n
  {
    var mb := new Mailbox(n);
    userboxList := [mb] + userboxList;
  }

  method newMessage(s: Address)
    requires Valid()
    modifies this.drafts
    ensures exists m: Message {:trigger m.sender} {:trigger m in drafts.messages} | m in drafts.messages :: m.sender == s
    decreases s
  {
    var m := new Message(s);
    drafts.add(m);
  }

  method moveMessage(m: Message, mb1: Mailbox, mb2: Mailbox)
    requires Valid()
    requires m in mb1.messages
    requires m !in mb2.messages
    modifies mb1, mb2
    ensures m !in mb1.messages
    ensures m in mb2.messages
    decreases m, mb1, mb2
  {
    mb1.remove(m);
    mb2.add(m);
  }

  method deleteMessage(m: Message, mb: Mailbox)
    requires Valid()
    requires m in mb.messages
    requires m !in trash.messages
    modifies m, mb, this.trash
    decreases m, mb
  {
    moveMessage(m, mb, trash);
  }

  method sendMessage(m: Message)
    requires Valid()
    requires m in drafts.messages
    requires m !in sent.messages
    modifies this.drafts, this.sent
    decreases m
  {
    moveMessage(m, drafts, sent);
  }

  method emptyTrash()
    requires Valid()
    modifies this.trash
    ensures trash.messages == {}
  {
    trash.empty();
  }
}
