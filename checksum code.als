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
