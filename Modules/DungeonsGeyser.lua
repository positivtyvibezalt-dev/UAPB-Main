local DungeonsTiming = getfenv().DungeonsTiming

return function(self, timing)
	return DungeonsTiming.run(self, timing, "Geyser", function(data)
		if not DungeonsTiming.number(data.Delay) then
			return
		end
		return { { when = data.Delay, origin = data.CF } }
	end)
end
