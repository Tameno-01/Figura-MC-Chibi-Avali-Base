-- PARAMETERS --

local STRETCH_STIFFNESS = 0.5
local STETCH_DAMPING = 1.4
local STRETCH_JUMP_IMPULSE = 0.3
local STRETCH_LAND_IMPULSE = 0.04
local STRETCH_MIN_LAND_IMPULSE = -0.7
local STRETCH_SIT_IMPULSE = -0.2
local STRETCH_UNSIT_IMPULSE = 0.2
local WADDLE_MULTIPLIER = 0.1
local SNEAKING_WADDLE_MULTIPLIER = 0.3
local WADDLE_MULTIPLIER_CHANGE_SPEED = 0.02
local SPRINT_ANIM_BLEND_CHANGE_SPEED = 0.25
local TAIL_STIFFNESS = 0.5
local TAIL_DAMPING = 2
local TAIL_CURVATURE = 20
local TAIL_END_MAX_PLAYER_DIST = 100

-- UTILS --

local asin, atan2, abs = math.asin, math.atan2, math.abs, math.deg
local pi = math.pi

function degSin(x)
	return math.sin(math.rad(x))
end

function degCos(x)
	return math.cos(math.rad(x))
end

function sign(x)
	if x < 0 then
		return -1
	else
		return 1
	end
end

function isMatNan(mat)
	for i = 1, 3 do
		column = mat:getColumn(i)
		if column.x ~= column.x then
			return true
		end
		if column.y ~= column.y then
			return true
		end
		if column.z ~= column.z then
			return true
		end
	end
	return false
end

function moveToward(from, to, delta)
	local diff = to - from
	if math.abs(diff) < delta then
		return to
	end
	return from + sign(diff) * delta
end

function matVecMul(mat, vect)
	local output = vec(0, 0, 0)
	output:add(mat:getColumn(1):mul(vect.x, vect.x, vect.x))
	output:add(mat:getColumn(2):mul(vect.y, vect.y, vect.y))
	output:add(mat:getColumn(3):mul(vect.z, vect.z, vect.z))
	return output
end

function eulerToMat(vect)
	local output = matrices.mat3()
	output:rotateX(vect.x)
	output:rotateY(vect.y)
	output:rotateZ(vect.z)
	return output
end

-- Thanks to @penguinencounter on discord for this function
---@param mat Matrix4|Matrix3
---@return Vector3
local function matToEuler(mat)
    ---@type number, number, number
    local x, y, z
    local query = mat.v31 -- are we in Gimbal Lock?
    if abs(query) < 0.9999 then
        y = asin(-mat.v31)
        z = atan2(mat.v21, mat.v11)
        x = atan2(mat.v32, mat.v33)
    elseif query < 0 then -- approx -1, gimbal lock
        y = pi / 2
        z = -atan2(-mat.v23, mat.v22)
        x = 0
    else -- approx 1, gimbal lock
        y = -pi / 2
        z = atan2(-mat.v23, mat.v22)
        x = 0
    end
    return vec(x, y, z):toDeg()
end

function getPartLocalPos(part)
	return part:getPivot():sub(part:getParent():getPivot())
end

function getPlayerPos(delta)
	delta = delta or 1
	return player:getPos(delta):mul(vec(16, 16, 16))
end

function getPlayerSpeed()
	return player:getVelocity():mul(vec(16, 16, 16))
end

-- SETUP --

local root = models.model.root
local waddlePivot = root.WaddlePivot
local body = waddlePivot.Body
local backFluff = body.BackFluff
local tail1 = backFluff.Tail1
local tail2 = tail1.Tail2
local tail3 = tail2.Tail3
local tailLeaf = tail3.TailLeaf
local leftArm = root.LeftArm
local rightArm = root.RightArm
local leftLeg = root.LeftLeg
local rightLeg = root.RightLeg
local head = root.Head

local flyAnim = animations.model.Fly
local flyTwirlAnim = animations.model.FlyTwirl
local sprintAnim = animations.model.Sprint
local sitAnim = animations.model.Sit

local leftKey = keybinds:fromVanilla("key.left")
local rightKey = keybinds:fromVanilla("key.right")
local backKey = keybinds:fromVanilla("key.back")
local forwardKey = keybinds:fromVanilla("key.forward")

function getPartWorldSpaceTransform(part, delta, modelMat)
	if part == root then
		-- We purposefully ignore the scaling of root
		local pos = getPlayerPos(delta)
		return getPlayerPos(delta), modelMat:copy():rightMultiply(
			eulerToMat(
				root:getTrueRot()
			)
		)
	end
	local pos, mat = getPartWorldSpaceTransform(part:getParent(), delta, modelMat)
	local localPos = getPartLocalPos(part)
	localPos:add(part:getTruePos())
	pos:add(matVecMul(mat, localPos))
	local trueRot = part:getTrueRot()
	if part == body then
		trueRot:add(vanilla_model.BODY:getOriginRot())
	end
	if part == leftArm then
		trueRot:add(vanilla_model.LEFT_ARM:getOriginRot())
	end
	if part == rightArm then
		trueRot:add(vanilla_model.RIGHT_ARM:getOriginRot())
	end
	if part == leftLeg then
		trueRot:add(vanilla_model.LEFT_LEG:getOriginRot())
	end
	if part == rightLeg then
		trueRot:add(vanilla_model.RIGHT_LEG:getOriginRot())
	end
	if part == head then
		trueRot:add(vanilla_model.HEAD:getOriginRot())
	end
	mat:rightMultiply(eulerToMat(trueRot))
	return pos, mat
end

vanilla_model.ALL:setVisible(false)
vanilla_model.HELD_ITEMS:setVisible(true)
vanilla_model.HELMET_ITEM:setVisible(true)

-- LOGIC --

local prevSpeed = vec(0, 0, 0)

local stretch = 1
local stretchSpeed = 0
local prevStretch

local onGround = true

local heldItemLastTickMainHand
local heldItemLastTickOffHand

local actualWaddleMultiplier = 0
local prevActualWaddleMultiplier

local sprintAnimBlend = 0
local prevSprintAnimBlend

local tailParts = {tail1, tail2, tail3}
local tailEnds = {}
local prevTailEnds = {}
local tailEndSpeeds = {}
local tailLengths = {}

local lastRenderMat = matrices:mat3()

function events.entity_init()
    heldItemLastTickMainHand = player:getHeldItem(false)
	heldItemLastTickOffHand = player:getHeldItem(true)
end

function getHeldItemLastTick(offhand)
	if offhand then
		return heldItemLastTickOffHand
	else
		return heldItemLastTickMainHand
	end
end

function processStretch()
	stretchSpeed = stretchSpeed - (stretch - 1) * STRETCH_STIFFNESS
	stretchSpeed = stretchSpeed / STETCH_DAMPING
	stretch = stretch + stretchSpeed
end

function goAirborne()
	onGround = false
	if getPlayerSpeed().y > 4 then -- JUMP
		stretchSpeed = STRETCH_JUMP_IMPULSE
	end
end

function land()
	onGround = true
	local stretchImpulse = prevSpeed.y * STRETCH_LAND_IMPULSE
	if stretchImpulse < STRETCH_MIN_LAND_IMPULSE then
		stretchImpulse = STRETCH_MIN_LAND_IMPULSE
	end
	stretchSpeed = stretchImpulse
end

function detectElytraBoost()
	if not player:isGliding() then
		return
	end
	if player:getSwingTime() ~= 1 then
		return
	end
	local item = getHeldItemLastTick(player:getSwingArm() == "OFF_HAND")
	if item:getID() == "minecraft:firework_rocket" then
		elytraBoost()
	end
end

function elytraBoost()
	flyTwirlAnim:play()
end

function getIdealWaddleMultiplier()
	if player:isSprinting() then
		return 0
	end
	if not (
		player:getPose() == "STANDING"
		or player:getPose() == "CROUCHING"
	) then
		return 0
	end
	if not onGround then
		return 0
	end
	if player:isSneaking() then
		return SNEAKING_WADDLE_MULTIPLIER
	else
		return WADDLE_MULTIPLIER
	end
end

function getIdealSprintBlend()
	if not player:isSprinting() then
		return 0
	end
	if player:isSneaking() then
		return 0
	end
	if player:isGliding() then
		return 0
	end
	if player:isBlocking() then
		return 0
	end
	if player:isVisuallySwimming() then
		return 0
	end
	return 1
end

function getTargetTailEnd(idx)
	local prevPoint
	if idx == 1 then
		local pos, mat = getPartWorldSpaceTransform(tail1, 1, lastRenderMat)
		prevPoint = pos
	else
		prevPoint = tailEnds[idx - 1]:copy()
	end
	local targetDir = vec(
		0,
		degSin(TAIL_CURVATURE * idx),
		degCos(TAIL_CURVATURE * idx)
	)
	local rootPos, rootMat = getPartWorldSpaceTransform(backFluff, 1, lastRenderMat)
	targetDir = matVecMul(rootMat, targetDir)
	local tailLength = tailLengths[idx]
	targetDir:mul(tailLength, tailLength, tailLength)
	return prevPoint:add(targetDir)
end

function processTail()
	for i = 1, #tailEnds do
		tailEnds[i]:sub(getPlayerPos())
		if tailEnds[i]:length() > TAIL_END_MAX_PLAYER_DIST then
			tailEnds[i]:normalize()
			tailEnds[i]:mul(
				TAIL_END_MAX_PLAYER_DIST,
				TAIL_END_MAX_PLAYER_DIST,
				TAIL_END_MAX_PLAYER_DIST
			)
		end
		tailEnds[i]:add(getPlayerPos())
		local force = getTargetTailEnd(i):sub(tailEnds[i])
		force:mul(TAIL_STIFFNESS, TAIL_STIFFNESS, TAIL_STIFFNESS)
		tailEndSpeeds[i]:add(force)
		tailEndSpeeds[i]:div(TAIL_DAMPING, TAIL_DAMPING, TAIL_DAMPING)
		tailEnds[i]:add(tailEndSpeeds[i])
	end
end

function events.entity_init()
	for i = 1, #tailParts do
		tailEnds[i] = getPlayerPos()
		tailEndSpeeds[i] = vec(0, 0, 0)
		if i == #tailParts then
			tailLengths[i] = getPartLocalPos(tailLeaf):length()
		else
			tailLengths[i] = getPartLocalPos(tailParts[i+1]):length()
		end
	end
	-- Avoiding errors, just in case...
	heldItemLastTickMainHand = player:getHeldItem(false)
	heldItemLastTickOffHand = player:getHeldItem(true)
end

function events.tick()
	prevStretch = stretch
	prevActualWaddleMultiplier = actualWaddleMultiplier
	prevSprintAnimBlend = sprintAnimBlend
	for i = 1, #tailEnds do
		prevTailEnds[i] = tailEnds[i]:copy()
	end
	if onGround then
		if not player:isOnGround() then
			goAirborne()
		end
	else
		if player:isOnGround() then
			land()
		end
	end
	detectElytraBoost()
	processStretch()
	if flyTwirlAnim:isPlaying() and not player:isGliding() then
		flyTwirlAnim:stop()
	end
	actualWaddleMultiplier = moveToward(
		actualWaddleMultiplier,
		getIdealWaddleMultiplier(),
		WADDLE_MULTIPLIER_CHANGE_SPEED
	)
	sprintAnimBlend = moveToward(
		sprintAnimBlend,
		getIdealSprintBlend(),
		SPRINT_ANIM_BLEND_CHANGE_SPEED
	)
	processTail()
	prevSpeed = getPlayerSpeed()
	heldItemLastTickMainHand = player:getHeldItem(false)
	heldItemLastTickOffHand = player:getHeldItem(true)
end

function processWaddle(delta)
	waddle = vanilla_model.RIGHT_LEG:getOriginRot().x
	waddle = waddle * math.lerp(
		prevActualWaddleMultiplier,
		actualWaddleMultiplier,
		delta
	)
	waddlePivot:setRot(0, 0, waddle)
end

function renderTailPhysics(delta, mat)
	for i = 1, #tailEnds do
		local tailPart = tailParts[i]
		local parentPos, parentMat = getPartWorldSpaceTransform(
			tailPart:getParent(),
			delta,
			mat
		)
		parentMat = matrices.mat3(
			parentMat:getColumn(1):normalized(),
			parentMat:getColumn(2):normalized(),
			parentMat:getColumn(3):normalized()
		)
		local tailEnd = math.lerp(prevTailEnds[i], tailEnds[i], delta)
		local tailPos, tailMat = getPartWorldSpaceTransform(tailPart, delta, mat)
		local newMatZ = tailEnd:sub(tailPos):normalized()
		local newMatY = parentMat:getColumn(2)
		local newMatX = newMatY:crossed(newMatZ):normalized()
		newMatY = newMatZ:crossed(newMatX):normalized()
		local newMat = matrices:mat3(newMatX, newMatY, newMatZ)
		newMat:multiply(parentMat:inverted())
		tailPart:setRot(matToEuler(newMat))
	end
end

function events.render(delta, context, matrix)
	matrix = matrices.mat4(
		matrix:getColumn(1):mul(-1, -1, -1, -1),
		matrix:getColumn(2):mul(-1, -1, -1, -1),
		matrix:getColumn(3),
		matrix:getColumn(4)
	):deaugmented()
	local stretchNow = math.lerp(prevStretch, stretch, delta)
	root:setScale(1/stretchNow, stretchNow, 1/stretchNow)
	processWaddle(delta)
	flyAnim:setPlaying(player:isGliding() and not flyTwirlAnim:isPlaying())
	local sprintAnimBlendNow = math.lerp(prevSprintAnimBlend, sprintAnimBlend, delta)
	sprintAnim:setPlaying(sprintAnimBlendNow ~= 0)
	sprintAnim:setBlend(sprintAnimBlendNow)
	renderTailPhysics(delta, matrix)
	if context ~= "FIRST_PERSON" and not isMatNan(matrix) then
		lastRenderMat = matrix
	end
end

-- HOST ONLY --

if host:isHost() then

	local sitting = false

	function shouldSit()
		if not player:isSneaking() then
			return false
		end
		if host:isFlying() then
			return false
		end
		if player:isBlocking() then
			return false
		end
		if (
			leftKey:isPressed()
			or rightKey:isPressed()
			or backKey:isPressed()
			or forwardKey:isPressed()
		) then
			return false
		end
		return true
	end

	function events.tick()
		if sitting then
			if not shouldSit() then
				sitting = false
				pings.unsit()
			end
		else
			if shouldSit() then
				sitting = true
				pings.sit()
			end
		end
	end

	function events.render(delta, context, matrix)
		if context == "FIRST_PERSON" then
			sitAnim:setPlaying(false)
			vanilla_model.HELD_ITEMS:setVisible(true)
		else
			sitAnim:setPlaying(sitting)
			vanilla_model.HELD_ITEMS:setVisible(not sitting)
		end
	end
	
end

-- PINGS --

function pings.sit()
	sitAnim:play()
	stretchSpeed = stretchSpeed + STRETCH_SIT_IMPULSE
	vanilla_model.HELD_ITEMS:setVisible(false)
end

function pings.unsit()
	sitAnim:stop()
	stretchSpeed = stretchSpeed + STRETCH_UNSIT_IMPULSE
	vanilla_model.HELD_ITEMS:setVisible(true)
end
