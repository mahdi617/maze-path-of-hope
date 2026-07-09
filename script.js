"use strict";


const canvas = document.getElementById("mazeCanvas");
const ctx = canvas.getContext("2d");

const sizeInput = document.getElementById("mazeSize");
const newMazeBtn = document.getElementById("newMazeBtn");
const undoBtn = document.getElementById("undoBtn");
const hintBtn = document.getElementById("hintBtn");
const messageEl = document.getElementById("message");
const gameStateEl = document.getElementById("gameState");
const moveCountEl = document.getElementById("moveCount");
const undoCountEl = document.getElementById("undoCount");
const hintCountEl = document.getElementById("hintCount");
const sizePreviewEl = document.getElementById("sizePreview");
const touchMoveButtons = document.querySelectorAll("[data-move]");
const touchActionButtons = document.querySelectorAll("[data-game-action]");

const DIRECTIONS = {
  north: { dx: 0, dy: -1, opposite: "south", label: "بالا" },
  south: { dx: 0, dy: 1, opposite: "north", label: "پایین" },
  east: { dx: 1, dy: 0, opposite: "west", label: "راست" },
  west: { dx: -1, dy: 0, opposite: "east", label: "چپ" }
};

const KEY_TO_DIRECTION = {
  w: "north",
  ArrowUp: "north",
  s: "south",
  ArrowDown: "south",
  d: "east",
  ArrowRight: "east",
  a: "west",
  ArrowLeft: "west"
};

const colors = {
  background: "#ffffff",
  board: "#f8fafc",
  grid: "rgba(148, 163, 184, 0.18)",
  wall: "#111827",
  start: "#dcfce7",
  finish: "#ffedd5",
  player: "#4f46e5",
  playerStroke: "#ffffff",
  crossroad: "#fef3c7",
  deadEnd: "#fee2e2",
  hintPath: "#dbeafe",
  nextHint: "#93c5fd",
  text: "#111827"
};

let maze = [];
let mazeSize = 16;
let cellSize = 24;
let offsetX = 0;
let offsetY = 0;
let player = { x: 0, y: 0 };
let start = { x: 0, y: 0 };
let finish = { x: 15, y: 15 };
let undoStack = [];
let hintPath = [];
let highlightedHintCell = null;
let gameStatus = "playing";
let moveCount = 0;
let undoCount = 0;
let hintCount = 0;

// هر خانه وضعیت دیوارها و بازدید شدن در الگوریتم DFS را نگه می‌دارد.
function createCell(x, y) {
  return {
    x,
    y,
    visited: false,
    walls: {
      north: true,
      south: true,
      east: true,
      west: true
    }
  };
}

// صفحه بازی به‌صورت یک ماتریس دوبعدی از خانه‌ها نگهداری می‌شود.
function createEmptyMaze(size) {
  return Array.from({ length: size }, (_, y) =>
    Array.from({ length: size }, (_, x) => createCell(x, y))
  );
}

function isInsideMaze(x, y) {
  return x >= 0 && y >= 0 && x < mazeSize && y < mazeSize;
}

function getCell(position) {
  return maze[position.y][position.x];
}

function positionsEqual(first, second) {
  return first.x === second.x && first.y === second.y;
}

function positionKey(position) {
  return `${position.x},${position.y}`;
}

function copyPosition(position) {
  return { x: position.x, y: position.y };
}

function toPersianDigits(value) {
  return String(value).replace(/\d/g, digit => "۰۱۲۳۴۵۶۷۸۹"[digit]);
}

function shuffle(items) {
  const shuffled = [...items];
  for (let i = shuffled.length - 1; i > 0; i -= 1) {
    const j = Math.floor(Math.random() * (i + 1));
    [shuffled[i], shuffled[j]] = [shuffled[j], shuffled[i]];
  }
  return shuffled;
}

/*
  Recursive Backtracking / DFS maze generation.
  A stack is used instead of recursive function calls to avoid call-stack limits
  when the user selects a large maze size.
*/
function generateMaze(size) {
  mazeSize = size;
  maze = createEmptyMaze(size);

  const stack = [maze[0][0]];
  maze[0][0].visited = true;

  while (stack.length > 0) {
    const current = stack[stack.length - 1];
    const unvisitedNeighbors = [];

    for (const [directionName, direction] of Object.entries(DIRECTIONS)) {
      const nx = current.x + direction.dx;
      const ny = current.y + direction.dy;

      if (isInsideMaze(nx, ny) && !maze[ny][nx].visited) {
        unvisitedNeighbors.push({ directionName, cell: maze[ny][nx] });
      }
    }

    if (unvisitedNeighbors.length === 0) {
      stack.pop();
      continue;
    }

    const selected = shuffle(unvisitedNeighbors)[0];
    current.walls[selected.directionName] = false;
    selected.cell.walls[DIRECTIONS[selected.directionName].opposite] = false;
    selected.cell.visited = true;
    stack.push(selected.cell);
  }

  // Generation-only visit flags are cleared so gameplay algorithms start cleanly.
  for (const row of maze) {
    for (const cell of row) {
      cell.visited = false;
    }
  }
}

function canMoveFrom(position, directionName) {
  const direction = DIRECTIONS[directionName];
  const nextX = position.x + direction.dx;
  const nextY = position.y + direction.dy;
  return isInsideMaze(nextX, nextY) && !getCell(position).walls[directionName];
}

function movePosition(position, directionName) {
  const direction = DIRECTIONS[directionName];
  return {
    x: position.x + direction.dx,
    y: position.y + direction.dy
  };
}

function getOpenNeighbors(position) {
  const neighbors = [];

  for (const directionName of Object.keys(DIRECTIONS)) {
    if (canMoveFrom(position, directionName)) {
      neighbors.push({
        directionName,
        position: movePosition(position, directionName)
      });
    }
  }

  return neighbors;
}

function isDeadEnd(position) {
  if (positionsEqual(position, start) || positionsEqual(position, finish)) {
    return false;
  }
  return getOpenNeighbors(position).length === 1;
}

function isCrossroad(position) {
  return getOpenNeighbors(position).length >= 3;
}

/*
  BFS solves the maze from any source cell to any target cell.
  It is used by the hint system because BFS gives the shortest path in an
  unweighted graph.
*/
function solveMazeWithBfs(source, target) {
  const queue = [copyPosition(source)];
  const previous = new Map();
  previous.set(positionKey(source), null);

  while (queue.length > 0) {
    const current = queue.shift();

    if (positionsEqual(current, target)) {
      break;
    }

    for (const neighbor of getOpenNeighbors(current)) {
      const key = positionKey(neighbor.position);
      if (!previous.has(key)) {
        previous.set(key, current);
        queue.push(neighbor.position);
      }
    }
  }

  if (!previous.has(positionKey(target))) {
    return [];
  }

  const path = [];
  let current = copyPosition(target);

  while (current !== null) {
    path.push(current);
    current = previous.get(positionKey(current));
  }

  return path.reverse();
}

function directionBetween(first, second) {
  for (const [directionName, direction] of Object.entries(DIRECTIONS)) {
    if (first.x + direction.dx === second.x && first.y + direction.dy === second.y) {
      return directionName;
    }
  }
  return null;
}

/*
  This branch analysis supports the assignment's "crossroad help" requirement.
  In a perfect maze, only one direction from a crossroad can be on the route to
  the destination. Other branches eventually contain dead ends, so the game can
  warn the player about those choices.
*/
function countDeadEndsInBranch(entryPosition, blockedPosition) {
  const stack = [entryPosition];
  const visited = new Set([positionKey(blockedPosition)]);
  let deadEnds = 0;
  let reachesFinish = false;

  while (stack.length > 0) {
    const current = stack.pop();
    const key = positionKey(current);

    if (visited.has(key)) {
      continue;
    }

    visited.add(key);

    if (positionsEqual(current, finish)) {
      reachesFinish = true;
    }

    if (isDeadEnd(current)) {
      deadEnds += 1;
    }

    for (const neighbor of getOpenNeighbors(current)) {
      if (!visited.has(positionKey(neighbor.position))) {
        stack.push(neighbor.position);
      }
    }
  }

  return { deadEnds, reachesFinish };
}

function resizeCanvasToDisplaySize() {
  const rect = canvas.getBoundingClientRect();
  const pixelRatio = window.devicePixelRatio || 1;
  const width = Math.floor(rect.width * pixelRatio);
  const height = Math.floor(rect.height * pixelRatio);

  if (canvas.width !== width || canvas.height !== height) {
    canvas.width = width;
    canvas.height = height;
  }

  ctx.setTransform(pixelRatio, 0, 0, pixelRatio, 0, 0);
}

function calculateLayout() {
  const rect = canvas.getBoundingClientRect();
  const padding = 28;
  const available = Math.min(rect.width, rect.height) - padding * 2;

  cellSize = Math.max(8, Math.floor(available / mazeSize));
  const mazePixels = cellSize * mazeSize;
  offsetX = Math.floor((rect.width - mazePixels) / 2);
  offsetY = Math.floor((rect.height - mazePixels) / 2);
}

function drawCellBackground(position, fillStyle) {
  const x = offsetX + position.x * cellSize;
  const y = offsetY + position.y * cellSize;

  ctx.fillStyle = colors.background;
  ctx.fillRect(x, y, cellSize, cellSize);

  if (fillStyle !== colors.background) {
    const inset = Math.max(1, cellSize * 0.08);
    const radius = Math.max(3, cellSize * 0.18);
    drawRoundedRect(x + inset, y + inset, cellSize - inset * 2, cellSize - inset * 2, radius, fillStyle);
  }
}

function drawRoundedRect(x, y, width, height, radius, fillStyle) {
  const r = Math.min(radius, width / 2, height / 2);
  ctx.beginPath();
  ctx.moveTo(x + r, y);
  ctx.lineTo(x + width - r, y);
  ctx.quadraticCurveTo(x + width, y, x + width, y + r);
  ctx.lineTo(x + width, y + height - r);
  ctx.quadraticCurveTo(x + width, y + height, x + width - r, y + height);
  ctx.lineTo(x + r, y + height);
  ctx.quadraticCurveTo(x, y + height, x, y + height - r);
  ctx.lineTo(x, y + r);
  ctx.quadraticCurveTo(x, y, x + r, y);
  ctx.closePath();
  ctx.fillStyle = fillStyle;
  ctx.fill();
}

function drawMaze() {
  resizeCanvasToDisplaySize();
  calculateLayout();

  const rect = canvas.getBoundingClientRect();
  ctx.clearRect(0, 0, rect.width, rect.height);
  ctx.fillStyle = colors.board;
  ctx.fillRect(0, 0, rect.width, rect.height);

  const mazePixels = cellSize * mazeSize;
  drawRoundedRect(offsetX - 10, offsetY - 10, mazePixels + 20, mazePixels + 20, 18, "#ffffff");

  const hintSet = new Set(hintPath.map(positionKey));

  // ابتدا رنگ خانه‌های مهم رسم می‌شود تا هزارتو خوانا بماند.
  for (let y = 0; y < mazeSize; y += 1) {
    for (let x = 0; x < mazeSize; x += 1) {
      const position = { x, y };
      let fill = colors.background;

      if (isDeadEnd(position)) fill = colors.deadEnd;
      if (isCrossroad(position)) fill = colors.crossroad;
      if (hintSet.has(positionKey(position))) fill = colors.hintPath;
      if (highlightedHintCell && positionsEqual(position, highlightedHintCell)) fill = colors.nextHint;
      if (positionsEqual(position, start)) fill = colors.start;
      if (positionsEqual(position, finish)) fill = colors.finish;

      drawCellBackground(position, fill);
    }
  }

  ctx.strokeStyle = colors.wall;
  ctx.lineWidth = Math.max(2, Math.floor(cellSize * 0.08));
  ctx.lineCap = "round";
  ctx.lineJoin = "round";

  for (const row of maze) {
    for (const cell of row) {
      const left = offsetX + cell.x * cellSize;
      const top = offsetY + cell.y * cellSize;
      const right = left + cellSize;
      const bottom = top + cellSize;

      ctx.beginPath();
      if (cell.walls.north) {
        ctx.moveTo(left, top);
        ctx.lineTo(right, top);
      }
      if (cell.walls.south) {
        ctx.moveTo(left, bottom);
        ctx.lineTo(right, bottom);
      }
      if (cell.walls.east) {
        ctx.moveTo(right, top);
        ctx.lineTo(right, bottom);
      }
      if (cell.walls.west) {
        ctx.moveTo(left, top);
        ctx.lineTo(left, bottom);
      }
      ctx.stroke();
    }
  }

  drawLabel(start, "ش", "#15803d");
  drawLabel(finish, "م", "#c2410c");
  drawPlayer();
}

function drawLabel(position, text, color) {
  ctx.fillStyle = color;
  ctx.font = `700 ${Math.max(11, Math.floor(cellSize * 0.48))}px Tahoma, Arial`;
  ctx.textAlign = "center";
  ctx.textBaseline = "middle";
  ctx.fillText(
    text,
    offsetX + position.x * cellSize + cellSize / 2,
    offsetY + position.y * cellSize + cellSize / 2
  );
}

function drawPlayer() {
  const centerX = offsetX + player.x * cellSize + cellSize / 2;
  const centerY = offsetY + player.y * cellSize + cellSize / 2;
  const radius = Math.max(5, cellSize * 0.31);

  ctx.save();
  ctx.shadowColor = "rgba(79, 70, 229, 0.38)";
  ctx.shadowBlur = Math.max(8, cellSize * 0.45);
  ctx.shadowOffsetY = Math.max(2, cellSize * 0.08);
  ctx.beginPath();
  ctx.arc(centerX, centerY, radius, 0, Math.PI * 2);
  ctx.fillStyle = colors.player;
  ctx.fill();
  ctx.restore();

  ctx.beginPath();
  ctx.arc(centerX, centerY, radius * 0.92, 0, Math.PI * 2);
  ctx.strokeStyle = colors.playerStroke;
  ctx.lineWidth = Math.max(2, cellSize * 0.1);
  ctx.stroke();
}

function updateStats() {
  moveCountEl.textContent = toPersianDigits(moveCount);
  undoCountEl.textContent = toPersianDigits(undoCount);
  hintCountEl.textContent = toPersianDigits(hintCount);

  if (sizePreviewEl) {
    sizePreviewEl.textContent = `${toPersianDigits(mazeSize)} × ${toPersianDigits(mazeSize)} خانه`;
  }
}

function setMessage(text, state = "playing") {
  messageEl.textContent = text;
  gameStateEl.textContent =
    state === "win" ? "تبریک! برنده شدید" :
    state === "lose" ? "پایان بازی" :
    "در حال بازی";

  gameStateEl.classList.toggle("state-win", state === "win");
  gameStateEl.classList.toggle("state-lose", state === "lose");
}

function startNewGame() {
  const requestedSize = Number.parseInt(sizeInput.value, 10);
  const safeSize = Number.isFinite(requestedSize)
    ? Math.min(40, Math.max(5, requestedSize))
    : 16;

  sizeInput.value = String(safeSize);
  generateMaze(safeSize);

  start = { x: 0, y: 0 };
  finish = { x: mazeSize - 1, y: mazeSize - 1 };
  player = copyPosition(start);
  undoStack = [];
  hintPath = [];
  highlightedHintCell = null;
  gameStatus = "playing";
  moveCount = 0;
  undoCount = 0;
  hintCount = 0;

  updateStats();
  setMessage("مسیر تازه ساخته شد. از خانه «ش» شروع کنید، به خانه «م» برسید و قبل از ورود به بن‌بست از راهنمایی کمک بگیرید.");
  drawMaze();
}

function endGame(status, text) {
  gameStatus = status;
  setMessage(text, status);
  drawMaze();
}

function movePlayer(directionName) {
  if (gameStatus !== "playing") {
    setMessage("بازی تمام شده است. برای شروع دوباره روی «هزارتوی جدید» بزنید.", gameStatus);
    return;
  }

  if (!canMoveFrom(player, directionName)) {
    setMessage("این مسیر بسته است. یک جهت باز دیگر را امتحان کنید.");
    return;
  }

  undoStack.push(copyPosition(player));
  player = movePosition(player, directionName);
  highlightedHintCell = null;
  hintPath = [];
  moveCount += 1;
  updateStats();

  if (positionsEqual(player, finish)) {
    endGame("win", "تبریک! مسیر را با موفقیت کامل کردید و به مقصد رسیدید.");
    return;
  }

  if (isDeadEnd(player)) {
    endGame("lose", "پایان بازی. به بن‌بست رسیدید و نمی‌توانید ادامه دهید.");
    return;
  }

  if (isCrossroad(player)) {
    setMessage("در یک چندراهی قرار دارید. برای راهنمایی، کلید فاصله را بزنید یا روی دکمه «راهنمایی» کلیک کنید.");
  } else {
    setMessage("حرکت انجام شد. به سمت مقصد ادامه دهید.");
  }

  drawMaze();
}

function undoMove() {
  if (undoStack.length === 0) {
    setMessage("هیچ حرکت قبلی برای بازگشت وجود ندارد.");
    return;
  }

  player = undoStack.pop();
  highlightedHintCell = null;
  hintPath = [];
  gameStatus = "playing";
  undoCount += 1;
  updateStats();
  setMessage("بازگشت به حرکت قبلی انجام شد.");
  drawMaze();
}

function showHint() {
  if (gameStatus !== "playing") {
    setMessage("برای گرفتن راهنمایی دوباره، ابتدا یک هزارتوی جدید بسازید.", gameStatus);
    return;
  }

  const path = solveMazeWithBfs(player, finish);
  if (path.length < 2) {
    setMessage("شما همین حالا در مقصد هستید.");
    return;
  }

  hintPath = path;
  highlightedHintCell = path[1];
  hintCount += 1;
  updateStats();

  const bestDirection = directionBetween(player, highlightedHintCell);
  const warnings = [];

  for (const neighbor of getOpenNeighbors(player)) {
    if (positionsEqual(neighbor.position, highlightedHintCell)) {
      continue;
    }

    const analysis = countDeadEndsInBranch(neighbor.position, player);
    if (!analysis.reachesFinish && analysis.deadEnds > 0) {
      warnings.push(`${DIRECTIONS[neighbor.directionName].label}: ${toPersianDigits(analysis.deadEnds)} بن‌بست`);
    }
  }

  const warningText = warnings.length > 0
    ? ` انتخاب‌های دیگر ممکن است خطرناک باشند (${warnings.join("؛ ")}).`
    : "";

  setMessage(`راهنمایی: به سمت ${DIRECTIONS[bestDirection].label} حرکت کنید. خانه درست بعدی مشخص شده است.${warningText}`);
  drawMaze();
}

function canvasPointToCell(event) {
  const rect = canvas.getBoundingClientRect();
  const x = Math.floor((event.clientX - rect.left - offsetX) / cellSize);
  const y = Math.floor((event.clientY - rect.top - offsetY) / cellSize);
  return { x, y };
}

function tryMouseMove(event) {
  if (gameStatus !== "playing") {
    return;
  }

  const clickedCell = canvasPointToCell(event);
  if (!isInsideMaze(clickedCell.x, clickedCell.y)) {
    return;
  }

  for (const neighbor of getOpenNeighbors(player)) {
    if (positionsEqual(neighbor.position, clickedCell)) {
      movePlayer(neighbor.directionName);
      return;
    }
  }

  setMessage("با ماوس فقط می‌توانید به خانه بازِ مجاور حرکت کنید.");
}

function handleKeyboard(event) {
  const codeToDirection = {
    KeyW: "north",
    KeyS: "south",
    KeyD: "east",
    KeyA: "west",
    ArrowUp: "north",
    ArrowDown: "south",
    ArrowRight: "east",
    ArrowLeft: "west"
  };

  const persianKeyToDirection = {
    ص: "north",
    س: "south",
    ی: "east",
    ش: "west"
  };

  const directionName = codeToDirection[event.code] || KEY_TO_DIRECTION[event.key] || persianKeyToDirection[event.key];

  if (directionName) {
    event.preventDefault();
    movePlayer(directionName);
    return;
  }

  if (event.key === " " || event.code === "Space") {
    event.preventDefault();
    showHint();
    return;
  }

  if (event.code === "KeyU" || event.key.toLowerCase() === "u" || event.key === "ع") {
    event.preventDefault();
    undoMove();
  }
}

newMazeBtn.addEventListener("click", startNewGame);
undoBtn.addEventListener("click", undoMove);
hintBtn.addEventListener("click", showHint);

if (sizeInput) {
  sizeInput.addEventListener("input", () => {
    const previewSize = Number.parseInt(sizeInput.value, 10);
    if (sizePreviewEl && Number.isFinite(previewSize)) {
      sizePreviewEl.textContent = `${toPersianDigits(Math.min(40, Math.max(5, previewSize)))} × ${toPersianDigits(Math.min(40, Math.max(5, previewSize)))} خانه`;
    }
  });
}

touchMoveButtons.forEach(button => {
  button.addEventListener("click", () => movePlayer(button.dataset.move));
});

touchActionButtons.forEach(button => {
  button.addEventListener("click", () => {
    if (button.dataset.gameAction === "hint") showHint();
    if (button.dataset.gameAction === "undo") undoMove();
  });
});
canvas.addEventListener("click", tryMouseMove);
window.addEventListener("keydown", handleKeyboard);
window.addEventListener("resize", drawMaze);

startNewGame();
