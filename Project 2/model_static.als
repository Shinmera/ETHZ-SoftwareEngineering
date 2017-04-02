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
 * Static model: Constraints
 */

//There can't be two airlines with the same name
fact airlinesUnique {
	all disjoint l, l': Airline | l.name != l'.name
}

//There can't be two airports with the same code
fact airportsUnique {
	all disjoint a, a': Airport | a.code != a'.code
}

//There can't be two bookings with the same id
fact bookingsUnique {
	all disjoint b, b': Booking | b.id != b'.id
}

//The next timestep can't be the time itself
fact timeNotSelf {
	all t: Time | t.after != t 
}

//There exists a last time state
fact endTimeMustBeLast {
	all disjoint t,t': Time | (no t.after) => (t in t'.^after)
}

//time is well ordered
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

//flight does not end at the same polace it starts
fact airportsDiffOverFlight {
	all f: Flight | f.departureAirport != f.arrivalAirport
}

//arrival is after departure
fact timesIncreaseOverFlight {
	all f: Flight | isBefore[f.departureTime, f.arrivalTime]
}

//in all bookings flights do not overlap
fact flightsDoNotOverlap {
	all b: Booking | all disj f,f': b.flights | isBefore[f.arrivalTime, f'.departureTime] or isBefore[f'.arrivalTime, f.departureTime] 
}

//for all aircrafts flights do not overlap
fact aircraftNotOverlap {
	all a: Aircraft | all disj f,f': getFlights[a] | isBefore[f.arrivalTime, f'.departureTime] or isBefore[f'.arrivalTime, f.departureTime]
}

//Roundtrip arrives at start airport
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

//a person is not in two flights at the same time
fact atNoTimePassengerOnTwoFlights {
	all disj f1, f2: Flight | all t: Time | #{p: Passenger | isInFlight[f1,p,t] and isInFlight[f2,p,t]} = 0 
}

//In every flight there is enough space for passengers in the correct classes
fact appropriateSeats {
	all f: Flight | #{p: Passenger, b: Booking | f in b.flights and p in b.passengers and b.category = FirstClass} <= #{s: f.aircraft.seats | s in FirstClassSeat}
	all f: Flight | #{p: Passenger, b: Booking | f in b.flights and p in b.passengers and (b.category = FirstClass or b.category = Business)} <= #{s: f.aircraft.seats | s in FirstClassSeat or s in BusinessSeat}
	all f: Flight | #{p: Passenger, b: Booking | f in b.flights and p in b.passengers and (b.category = FirstClass or b.category = Business or  b.category = Economy)} <= #{s: f.aircraft.seats | s in FirstClassSeat or s in BusinessSeat or s in EconomySeat}	
}

/*
 * Static model: Predicates
 */

// True iff t1 is strictly before t2.
pred isBefore[t1, t2: Time] {
	t2 in t1.^after
}

//checks for a class and a seat if a passenger in class c can be given the seat s
pred isAcceptableSeat[s: Seat, c: Class]{
	(s in FirstClassSeat and (c = FirstClass)) or
	(s in BusinessSeat and   (c = FirstClass or c = Business)) or
	(s in EconomySeat and    (c = FirstClass or c = Business or c = Economy))
}

//true if the aircraft is on the ground
pred aircraftOnGround[ac: Aircraft, t: Time] {
	 #{f: Flight | isInAir[f,t] and f.aircraft = ac} = 0
}

//true if the flight is in the air
pred isInAir[f: Flight, t: Time]{
	isBefore[getDeparture[f],t] and isBefore[t, getArrival[f]]
}

//checks if the passenger is on the flight f at time t
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
	#Time = 4
	#Aircraft = 1
	#Airline = 1
	#Booking = 1
	#RoundTrip = 0
	#Passenger = 1
	#Flight = 1
}

pred static_instance_1 {
	#Flight = 1
	#Aircraft = 1
	#Airline = 1
	#Passenger = 1
	#Seat = 1
	#Airport = 2
}

pred static_instance_2 {
	all disj x, y: Booking | x.category != y.category
	#Booking = 3
	#Seat = 2
	all disj s1, s2: Seat | (s1 in FirstClassSeat and s2 in FirstClassSeat) or
									   (s1 in BusinessSeat and   s2 in BusinessSeat) or
									   (s1 in EconomySeat and  s2 in EconomySeat )
	#Passenger = 2
	#Flight = 2
	#Airport = 2
	#Airline = 1
}

pred static_instance_3 {
	#RoundTrip = 1
	#RoundTrip.flights = 3
	#Seat = 1
	#Passenger = 1
	#Airport = 2
	#Airline = 1
}

pred static_instance_4 {
	#Booking = 2
	all disj b1, b2: Booking | getOrigin[getFirstFlight[b1]] != getOrigin[getFirstFlight[b2]]
	all disj b1, b2: Booking | getDestination[getLastFlight[b1]] != getDestination[getLastFlight[b2]]
	all disj b1, b2: Booking | #(b1.flights & b2.flights) > 0
	#Passenger = 2
	#Seat = 2
	#Airline = 1
}

pred static_instance_5 {
	#Booking = 1
	#Booking.flights = 3
	all b: Booking |getFirstFlight[b].aircraft = getLastFlight[b].aircraft
	#Booking.flights.aircraft = 2
	#Passenger = 1
	#Aircraft = 2
	#Seat = 2
	#Airline = 1
}

run show for 6
run static_instance_1 for 6
run static_instance_2 for 6
run static_instance_3 for 6
run static_instance_4 for 6
run static_instance_5 for 6

