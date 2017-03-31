/*
 * Static model: Signatures
 *
 * The model should contain the following (and potentially other) signatures.
 * If necessary, you have to make some of the signatures abstract and
 * make them extend other signatures.
 */

sig Str {}

sig Location {}
sig PassengerLocation extends Location {}
one sig Unknown in PassengerLocation {}
sig AircraftLocation extends Location {}
one sig InAir in AircraftLocation {}

sig Aircraft extends PassengerLocation{
	seats: some Seat
}

sig Airline {
	name: Str,
	aircraft: set Aircraft,
	flights: set Flight
}

sig Airport extends AircraftLocation{
	code: Str
}

sig Booking {
	id: Str,
	flights: some Flight,
	category: Class,
	passengers: some Passenger
}

enum Class {
	FirstClass,
	Business,
	Economy
}

sig Flight {
	number: Str,
	departureAirport: Airport,
	arrivalAirport: Airport,
	departureTime: Time,
	arrivalTime: Time,
	aircraft: Aircraft,
	passengers: some Passenger
}

sig Passenger {
	bookings: some Booking
}

sig RoundTrip extends Booking { }

abstract sig Seat {}
sig EconomySeat extends Seat {}
sig BusinessSeat extends EconomySeat {}
sig FirstClassSeat extends BusinessSeat {}

sig Time {
	after: lone Time
}

/*
 * Dynamic Model Signatures
 */

sig State{
	passengers: set Passenger,
	aircrafts: set Aircraft,
	passenger_locations: Passenger -> one PassengerLocation,
	aircraft_locations: Aircraft -> one AircraftLocation,
	time: Time
}


/*
 * Static model: Constraints
 */

fact airlinesUnique {
	all disjoint l, l': Airline | l.name != l'.name
}

fact airportsUnique {
	all disjoint a, a': Airport | a.code != a'.code
}

fact bookingsUnique {
	all disjoint b, b': Booking | b.id != b'.id
}

fact timeNotSelf {
	all t: Time | t.after != t 
}

fact endTimeMustBeLast {
	all disjoint t,t': Time | (no t.after) => (t in t'.^after)
}

fact timeLinearlyIncreasing {
	all disjoint t,t': Time | (t in t'.^after) iff not (t' in t.^after)
}

fact seatsBelong {
	all s: Seat | one a: Aircraft | s in a.seats
}

fact aircraftBelong {
	all a: Aircraft | one l: Airline | a in l.aircraft
}

fact operatorMustMatchAircraft {
	all f: Flight, l: Airline | (f.aircraft in l.aircraft) or (not f in l.flights)
}

fact airportsDiffOverFlight {
	all f: Flight | f.departureAirport != f.arrivalAirport
}

fact timesIncreaseOverFlight {
	all f: Flight | isBefore[f.departureTime, f.arrivalTime]
}

fact flightsDoNotOverlap {
	all b: Booking | all disj f,f': b.flights | isBefore[f.arrivalTime, f'.departureTime] or isBefore[f'.arrivalTime, f.departureTime] 
}

fact aircraftNotOverlap {
	all a: Aircraft | all disj f,f': getFlights[a] | isBefore[f.arrivalTime, f'.departureTime] or isBefore[f'.arrivalTime, f.departureTime]
}

fact roundtripMatches {
	all r: RoundTrip | getFirstFlight[r].departureAirport = getLastFlight[r].arrivalAirport
}

fact bookingsMatch {
	all p: Passenger, b: Booking | (b in p.bookings) iff (p in b.passengers)
}

fact atLeastOneAirline {
	all f: Flight | some l: Airline | f in l.flights
}

fact passengersMatch {
	all f: Flight | all p: f.passengers | f in p.bookings.flights
}

fact airportNotInAir {
	all a: Airport | a != InAir
}

fact aircraftNotUnknown {
	all a: Aircraft | a != Unknown
}


fact atNoTimePassengerOnTwoFlights {
	all disj f1, f2: Flight | all t: Time | #{p: Passenger | p in f1.passengers and isInFlight[f1,p,t] and isInFlight[f2,p,t] and p in f2.passengers} = 0 
}

// I don't think this is entirely correct.
fact appropriateSeats {
	all f: Flight | all p: f.passengers | one s: f.aircraft.seats, b: p.bookings | f in b.flights and isAcceptableSeat[s, b.category]
}

/*
 * Static model: Predicates
 */

// True iff t1 is strictly before t2.
pred isBefore[t1, t2: Time] {
	t2 in t1.^after
}

pred isAcceptableSeat[s: Seat, c: Class]{
	(s in FirstClassSeat and (c = FirstClass)) or
	(s in BusinessSeat and   (c = FirstClass or c = Business)) or
	(s in EconomySeat and    (c = FirstClass or c = Business or c = Economy))
}


pred aircraftOnGround[ac: Aircraft, t: Time] {
	 #{f: Flight | isInAir[f,t] and f.aircraft = ac} = 0
}

pred isInAir[f: Flight, t: Time]{
	isBefore[getDeparture[f],t] and isBefore[t, getArrival[f]]
}

pred isInFlight[f: Flight, p: Passenger, t: Time]{
	t in getDeparture[f].*after  and getArrival[f] in t.*after and p in f.passengers
}

/*
 * Static model: Functions
 */

// Returns the departure time of the given flight.
fun getDeparture[f: Flight]: Time { 
	f.departureTime
}

// Returns the arrival time of the given flight.
fun getArrival[f: Flight]: Time { 
	f.arrivalTime
}

// Returns the airport the given flight departs from.
fun getOrigin[f: Flight]: Airport { 
	f.departureAirport
}

// Returns the destination airport of the given flight. 
fun getDestination[f: Flight]: Airport {
	f.arrivalAirport
}

// Returns the first flight of the given booking.
fun getFirstFlight[b: Booking]: Flight {
	{f: b.flights | no {f': b.flights | (f != f') and isBefore[f'.departureTime, f.departureTime]}}
}

// Returns the last flight of the given booking.
fun getLastFlight[b: Booking]: Flight {
	{f: b.flights | no {f': b.flights | (f != f') and isBefore[f.departureTime, f'.departureTime]}}
}

// Returns all seats of the given aircraft. 
fun getSeats[a: Aircraft]: set Seat {
	a.seats
}

// Returns all flights for which is given aircraft is used.
fun getFlights[a: Aircraft]: set Flight {
	{f: Flight | f.aircraft = a}
}

// Returns all bookings booked by the given passenger.
fun getBookings[p: Passenger]: set Booking {
	p.bookings
}

// Returns all flights contained in the given booking.
fun getFlightsInBooking[b: Booking]: set Flight {
	b.flights
}

/*
 * Static model: Tests
 */

pred show {
	#Aircraft = 1
	#Airline = 1
	#Booking = 1
	#RoundTrip = 0
	#Passenger = 1
	#Flight = 1
}

run show for 6
/*
 * Dynamic model: Constraints
 */

fact exactlyOneStateForEveryTime {
	all disj s1, s2: State | s1.time != s2.time
	#State = #Time
}

fact aircraftInAirWhileFlight {
	all f: Flight, t: Time | isInAir[f,t] => getAircraftLocation[t, f.aircraft] in InAir
}

fact aircraftAtDepartureAirport {
	all f: Flight | getAircraftLocation[getDeparture[f],f.aircraft] = getOrigin[f]
}

fact aircraftAtDestinationAirport {
	all f: Flight | getAircraftLocation[getArrival[f],f.aircraft] = getDestination[f]
}

fact aircraftLocationOnGroundDoesntChange {
	all ac: Aircraft, t1, t2: Time | (t1.after = t2 and aircraftOnGround[ac,t1] and aircraftOnGround[ac,t2] ) => getAircraftLocation[t1,ac] = getAircraftLocation[t2, ac]
}

fact aircraftOnGroundWhileNotInFlight {
	all ac: Aircraft, t: Time |aircraftOnGround[ac,t] => getAircraftLocation[t,ac] in Airport
}

fact personInAircraftWhileInFlight {
	all f: Flight, p: Passenger , t: Time |  isInFlight[f,p,t] => getPassengerLocation[t, p] = f.aircraft
}

fact personSomewhereUnknownWhileNotInFlight {
	all p: Passenger, t:Time | (#{f: Flight | isInFlight[f,p,t]}=0)  => getPassengerLocation[t, p] in Unknown
}


/*
 * Dynamic Predicates
 */

/*
 * Dynamic model: Functions
 */

// Returns the state which comes after the given state.
fun getNextState[s: State]: State {
	{s1: State | s.time.after = s1.time}
} 

//Returns the State corresponding to a Time [added]
fun getState[t: Time]: State{
	{s: State | s.time = t}
}

// Returns the location of the given passenger at the given time. 
fun getPassengerLocation[t: Time, p: Passenger]: PassengerLocation {
	getState[t].passenger_locations[p]
}

// Returns the location of the given aircraft at the given time.
fun getAircraftLocation[t: Time, ac: Aircraft]: AircraftLocation {
	getState[t].aircraft_locations[ac]
}

// Returns the time whose state the given State represents.
fun getTime[s: State]: Time {
	s.time
}


/*
 * Dynamic model: Tests
 */
pred dynamic_instance_1 {
	some p: Passenger | #{f: Flight | p in f.passengers} > 1
	#Flight = 3
	#Passenger = 1
	#RoundTrip = 1
	#Airport = 2
}

pred dynamic_instance_2 {
	some ac: Aircraft, p: Passenger| #{t: Time | getPassengerLocation[t,p] in Unknown and getAircraftLocation[t,ac] in InAir} > 0
	#Booking = 1
	#Flight = 2
}

pred dynamic_instance_3 {
	all t: Time | all disj p1,p2: Passenger | getPassengerLocation[t,p1]= getPassengerLocation[t,p2]
	all disj b: Booking,  p1,p2: Passenger |  p1 in b.passengers => not (p2 in b.passengers)
	all rt: RoundTrip, b: Booking, p: Passenger | ((b != rt) and (p in rt.passengers)) => not p in b.passengers
	#RoundTrip = 1
	#Booking = 3
	#Aircraft = 2
	#Airport = 2
	#Passenger = 2
}

run dynamic_instance_1 for 6
run dynamic_instance_2 for 6
run dynamic_instance_3 for 6
