// CO3408-Advanced-Software-Modelling-Assignment-2022-23-Part-2-A-Specification-Spectacular_tmp_tmp4pj4p2zx_car_park.dfy

method Main()
{
  var carPark := new CarPark();
  var availableSpaces := carPark.checkAvailability();
  assert availableSpaces == 2;
  var success := carPark.enterCarPark("car1");
  availableSpaces := carPark.checkAvailability();
  assert success && carPark.carPark == {"car1"} && availableSpaces == 1;
  success := carPark.enterCarPark("car2");
  availableSpaces := carPark.checkAvailability();
  assert success && "car2" in carPark.carPark && carPark.carPark == {"car1", "car2"} && availableSpaces == 0;
  success := carPark.enterCarPark("car3");
  assert !success && carPark.carPark == {"car1", "car2"} && carPark.reservedCarPark == {};
  success := carPark.makeSubscription("car4");
  assert success && carPark.subscriptions == {"car4"};
  success := carPark.enterReservedCarPark("car4");
  assert success && carPark.reservedCarPark == {"car4"};
  success := carPark.enterReservedCarPark("car5");
  assert !success && carPark.reservedCarPark == {"car4"};
  success := carPark.makeSubscription("car6");
  assert success && carPark.subscriptions == {"car4", "car6"};
  success := carPark.makeSubscription("car7");
  assert success && carPark.subscriptions == {"car4", "car6", "car7"};
  success := carPark.makeSubscription("car8");
  assert !success && carPark.subscriptions == {"car4", "car6", "car7"};
  success := carPark.enterReservedCarPark("car6");
  assert success && carPark.reservedCarPark == {"car4", "car6"};
  success := carPark.enterReservedCarPark("car7");
  assert success && carPark.reservedCarPark == {"car4", "car6", "car7"};
  assert carPark.carPark == {"car1", "car2"};
  success := carPark.leaveCarPark("car1");
  assert success && carPark.carPark == {"car2"} && carPark.reservedCarPark == {"car4", "car6", "car7"};
  assert "car9" !in carPark.carPark && "car9" !in carPark.reservedCarPark;
  success := carPark.leaveCarPark("car9");
  assert !success && carPark.carPark == {"car2"} && carPark.reservedCarPark == {"car4", "car6", "car7"};
  success := carPark.leaveCarPark("car6");
  assert success && carPark.carPark == {"car2"} && carPark.reservedCarPark == {"car4", "car7"};
  carPark.closeCarPark();
  assert carPark.carPark == {} && carPark.reservedCarPark == {} && carPark.subscriptions == {};
}

method MainB()
{
  var carPark := new CarPark();
  assert carPark.weekend == false;
  carPark.openReservedArea();
  assert carPark.weekend == true;
  var success := carPark.enterReservedCarPark("car3");
  assert "car3" !in carPark.subscriptions && success && carPark.carPark == {} && carPark.reservedCarPark == {"car3"};
  carPark.closeCarPark();
  assert carPark.carPark == {} && carPark.reservedCarPark == {} && carPark.subscriptions == {};
}

class {:autocontracts} CarPark {
  const totalSpaces: nat := 10
  const normalSpaces: nat := 7
  const reservedSpaces: nat := 3
  const badParkingBuffer: int := 5
  var weekend: bool
  var subscriptions: set<string>
  var carPark: set<string>
  var reservedCarPark: set<string>

  constructor ()
    requires true
    ensures Valid()
    ensures fresh(Repr)
    ensures this.subscriptions == {} && this.carPark == {} && this.reservedCarPark == {} && this.weekend == false
  {
    this.subscriptions := {};
    this.carPark := {};
    this.reservedCarPark := {};
    this.weekend := false;
    new;
    Repr := {this};
  }

  ghost predicate Valid()
    reads this, this, Repr
    ensures Valid() ==> this in Repr
    decreases Repr + {this, this}
  {
    this in Repr &&
    null !in Repr &&
    carPark * reservedCarPark == {} &&
    |carPark| <= totalSpaces + badParkingBuffer &&
    normalSpaces + reservedSpaces == totalSpaces &&
    |reservedCarPark| <= reservedSpaces
  }

  method leaveCarPark(car: string) returns (success: bool)
    requires Valid()
    requires true
    modifies this
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures success ==> (car in old(carPark) && carPark == old(carPark) - {car} && reservedCarPark == old(reservedCarPark)) || (car in old(reservedCarPark) && reservedCarPark == old(reservedCarPark) - {car} && carPark == old(carPark))
    ensures success ==> car !in carPark && car !in reservedCarPark
    ensures !success ==> carPark == old(carPark) && reservedCarPark == old(reservedCarPark) && car !in old(carPark) && car !in old(reservedCarPark)
    ensures subscriptions == old(subscriptions) && weekend == old(weekend)
    decreases car
  {
    success := false;
    if car in carPark {
      carPark := carPark - {car};
      success := true;
    } else if car in reservedCarPark {
      reservedCarPark := reservedCarPark - {car};
      success := true;
    }
  }

  method checkAvailability() returns (availableSpaces: int)
    requires Valid()
    requires true
    modifies this
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures weekend ==> availableSpaces == normalSpaces - old(|carPark|) + reservedSpaces - old(|reservedCarPark|) - badParkingBuffer
    ensures !weekend ==> availableSpaces == normalSpaces - old(|carPark|) - badParkingBuffer
    ensures carPark == old(carPark) && reservedCarPark == old(reservedCarPark) && weekend == old(weekend) && subscriptions == old(subscriptions)
  {
    if weekend {
      availableSpaces := normalSpaces - |carPark| + reservedSpaces - |reservedCarPark| - badParkingBuffer;
    } else {
      availableSpaces := normalSpaces - |carPark| - badParkingBuffer;
    }
  }

  method makeSubscription(car: string) returns (success: bool)
    requires Valid()
    requires true
    modifies this
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures success ==> old(|subscriptions|) < reservedSpaces && car !in old(subscriptions) && subscriptions == old(subscriptions) + {car}
    ensures !success ==> subscriptions == old(subscriptions) && (car in old(subscriptions) || old(|subscriptions|) >= reservedSpaces)
    ensures carPark == old(carPark) && reservedCarPark == old(reservedCarPark) && weekend == old(weekend)
    decreases car
  {
    if |subscriptions| >= reservedSpaces || car in subscriptions {
      success := false;
    } else {
      subscriptions := subscriptions + {car};
      success := true;
    }
  }

  method openReservedArea()
    requires Valid()
    requires true
    modifies this
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures carPark == old(carPark) && reservedCarPark == old(reservedCarPark) && weekend == true && subscriptions == old(subscriptions)
  {
    weekend := true;
  }

  method closeCarPark()
    requires Valid()
    requires true
    modifies this
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures carPark == {} && reservedCarPark == {} && subscriptions == {}
    ensures weekend == old(weekend)
  {
    carPark := {};
    reservedCarPark := {};
    subscriptions := {};
  }

  method enterCarPark(car: string) returns (success: bool)
    requires Valid()
    requires true
    modifies this
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures success ==> car !in old(carPark) && car !in old(reservedCarPark) && old(|carPark|) < normalSpaces - badParkingBuffer
    ensures success ==> carPark == old(carPark) + {car}
    ensures !success ==> carPark == old(carPark) && reservedCarPark == old(reservedCarPark)
    ensures !success ==> car in old(carPark) || car in old(reservedCarPark) || old(|carPark|) >= normalSpaces - badParkingBuffer
    ensures subscriptions == old(subscriptions) && reservedCarPark == old(reservedCarPark) && weekend == old(weekend)
    decreases car
  {
    if |carPark| >= normalSpaces - badParkingBuffer || car in carPark || car in reservedCarPark {
      return false;
    } else {
      carPark := carPark + {car};
      return true;
    }
  }

  method enterReservedCarPark(car: string) returns (success: bool)
    requires Valid()
    requires true
    modifies this
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures success ==> car !in old(carPark) && car !in old(reservedCarPark) && old(|reservedCarPark|) < reservedSpaces && (car in subscriptions || weekend == true)
    ensures success ==> reservedCarPark == old(reservedCarPark) + {car}
    ensures !success ==> carPark == old(carPark) && reservedCarPark == old(reservedCarPark)
    ensures !success ==> car in old(carPark) || car in old(reservedCarPark) || old(|reservedCarPark|) >= reservedSpaces || (car !in subscriptions && weekend == false)
    ensures subscriptions == old(subscriptions) && carPark == old(carPark) && weekend == old(weekend)
    ensures weekend == old(weekend) && subscriptions == old(subscriptions)
    decreases car
  {
    if |reservedCarPark| >= reservedSpaces || car in carPark || car in reservedCarPark || car !in subscriptions {
      return false;
    } else {
      reservedCarPark := reservedCarPark + {car};
      return true;
    }
  }

  ghost var Repr: set<object?>
}
