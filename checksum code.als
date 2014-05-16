sig Packet{
	checksum: one Checksum
	payload: one Payload
}

pred simulateOneError[]{
	one p: Packet |
			p.checksum != p.payload.computeChecksum[]
...
...
...
}

one sig Global{
	checksums: Payload one -> one Checksum
}

fun computeChecksum [p: Payload] Checksum {
	Global.checksums[p]
}

/* SIDE NOTE

we need multiple Ack/Nak objects.

we need a skip in the transition if we get an Ack/Nak as the else statement
*/
