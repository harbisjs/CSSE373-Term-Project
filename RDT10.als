open util/ordering[SystemState]

sig Data{}

sig Packet{
	insideData: one Data
}

sig Sender{
	buffer: set Data
}

sig Reciever{
	buffer: set Data
}

sig SystemState{
	currentSender: one Sender,
	currentReciever: one Reciever,
	inFlight: lone Packet
}

pred sendPacket[s1, s2 : SystemState]{

		//the senders are different
		s1.currentSender in Sender - s2.currentSender
		and
		//the recievers are the same
		s1.currentReciever not in Reciever - s2.currentReciever

		and
		//initially nothing in flight
		(no p:Packet | p in s1.inFlight)
		and
		//after only one packet in flight
		(one p:Packet | p in s2.inFlight)


		and
		(
		one d: Data |
			//the data came from the sender buffer and is now in flight
			d in s2.inFlight.insideData and d in s1.currentSender.buffer
			//the data did not start in flight and did not end up in the sender buffer
			and d not in s2.currentSender.buffer and d not in s1.inFlight.insideData
			//the data is not in any reciever buffer
			and d not in s1.currentReciever.buffer and d not in s2.currentReciever.buffer
			
			and 
			// all data initially in the buffer other than the data sent is still in the buffer
			(all senderData : s1.currentSender.buffer - d | senderData in s2.currentSender.buffer)
			and
			// no new data entered the buffer
			(all senderData : Data - (s1.currentSender.buffer - d) | senderData not in s2.currentSender.buffer)
			and
			//nothing got lost from the reciever buffer
			(all recieverData : s1.currentReciever.buffer | recieverData in s2.currentReciever.buffer)
			and
			//nothing got added in the reciever buffer
			(all recieverData : Data - s1.currentReciever.buffer | recieverData not in s2.currentReciever.buffer)
		)
}

pred recievePacket[s1, s2: SystemState]{

		
		// the senders are the same
		s1.currentSender not in Sender - s2.currentSender
		and
		// the recievers are different
		s1.currentReciever in Reciever - s2.currentReciever

		and
		//initially one packet in flight
		(one p:Packet | p in s1.inFlight)
		and
		//after nothing in flight
		(no p:Packet | p in s2.inFlight)

		and
		(
		one d: Data |
			// the data was in flight and is now in the buffer			
			d in s1.inFlight.insideData and d in s2.currentReciever.buffer
			// the data was not initially in the reciever buffer and is no longer in flight
			and d not in s1.currentReciever.buffer and d not in s2.inFlight.insideData
			// the data was never in the sender buffer before or after
			and d not in s1.currentSender.buffer and d not in s2.currentSender.buffer
			
			and 
			// all data originally in the sender buffer is still in there
			(all senderData : s1.currentSender.buffer | senderData in s2.currentSender.buffer)
			and
			// no new data has entered the sender buffer
			(all senderData : Data - (s1.currentSender.buffer) | senderData not in s2.currentSender.buffer)
			and
			// all data that was either originally in the buffer or that has arrived is in the buffer
			(all recieverData : s1.currentReciever.buffer + d | recieverData in s2.currentReciever.buffer)
			and
			// no data other than what was originally in the buffer or has now arrived is in the new buffer
			(all recieverData : Data - (s1.currentReciever.buffer + d) | recieverData not in s2.currentReciever.buffer)
		)
}

pred finalState[s: SystemState]{
	s.currentReciever.buffer = Data 
	no s.currentSender.buffer
	no s.inFlight
}

pred init[s: SystemState]{
	s.currentSender.buffer = Data 
	no s.currentReciever.buffer
	no s.inFlight	
}


fact traceFullTransition{
	init[first]
	all s:SystemState - last |
		let s' = s.next |
			sendPacket[s, s'] or recievePacket[s, s']
}

fact trimExtraPackets{
	all d:Data| one p:Packet | d in p.insideData
}

fact trimExtraSenders{
	all disj s1, s2: Sender | s1.buffer not = s2.buffer
}

fact trimExtraRecievers{
	all disj s1, s2: Reciever | s1.buffer not = s2.buffer
}

pred allDataGetsThroughPred{
	some s: SystemState |
		finalState[s]
}

assert allDataGetsThrough{
	not( some s: SystemState |
		finalState[s])
}

pred failureState[s:SystemState] {
	no s.inFlight
	no s.currentSender.buffer
	some d:Data| d not in s.currentReciever.buffer
}

assert allDataDoesNotGetThrough{
	not some s:SystemState |	failureState[s]
}

check allDataGetsThrough for 5 but exactly 2 Data
check allDataDoesNotGetThrough for 5 but exactly 2 Data

run sendPacket for 2

run recievePacket for 2

run finalState for 5 but exactly 2 Data
run init for 3 but exactly 2 Data
