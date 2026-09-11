local DungeonsTiming = getfenv().DungeonsTiming

return function(self, timing)
	return DungeonsTiming.run(self, timing, "CrystallineEruption", function(data)
		if not DungeonsTiming.number(data.BlowDelay) then
			return
		end
		return { { when = data.BlowDelay, origin = data.Location } }
	end)
end
