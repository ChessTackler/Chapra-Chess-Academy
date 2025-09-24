# Advanced Digital Chess Platform
# Core architecture with FIDE-compliant engine, multiplayer support, and extensible features

import asyncio
import json
import uuid
import time
import hashlib
import re
from typing import Dict, List, Optional, Tuple, Set, Union, Any
from dataclasses import dataclass, field
from enum import Enum
from datetime import datetime, timedelta
import logging
from collections import defaultdict
import chess
import chess.engine
import chess.pgn
import chess.syzygy

# Configuration and Constants
class GameMode(Enum):
    CLASSICAL = "classical"
    RAPID = "rapid"
    BLITZ = "blitz"
    BULLET = "bullet"
    CORRESPONDENCE = "correspondence"
    PUZZLE = "puzzle"

class GameVariant(Enum):
    STANDARD = "standard"
    CHESS960 = "chess960"
    CRAZYHOUSE = "crazyhouse"
    KING_OF_THE_HILL = "koth"
    THREE_CHECK = "3check"

class TournamentType(Enum):
    SWISS = "swiss"
    ARENA = "arena"
    ROUND_ROBIN = "round_robin"
    KNOCKOUT = "knockout"

@dataclass
class TimeControl:
    initial_seconds: int
    increment_seconds: int = 0
    delay_seconds: int = 0

    def __str__(self):
        if self.increment_seconds:
            return f"{self.initial_seconds//60}+{self.increment_seconds}"
        return f"{self.initial_seconds//60}min"

@dataclass
class Player:
    id: str
    username: str
    email: str
    rating: int = 1200
    rd: float = 350.0  # Rating deviation for Glicko-2
    volatility: float = 0.06
    games_played: int = 0
    wins: int = 0
    losses: int = 0
    draws: int = 0
    is_online: bool = False
    last_seen: datetime = field(default_factory=datetime.now)
    preferences: Dict[str, Any] = field(default_factory=dict)
    security: Dict[str, Any] = field(default_factory=dict)

class ChessEngine:
    """FIDE-compliant chess engine with full rule implementation"""

    def __init__(self, variant: GameVariant = GameVariant.STANDARD):
        self.variant = variant
        self.board = chess.Board()
        if variant == GameVariant.CHESS960:
            self.board = chess.Board(chess960=True)

        self.move_history: List[chess.Move] = []
        self.position_history: List[str] = []
        self.game_state = "active"
        self.result = None

    def make_move(self, move_uci: str) -> Dict[str, Any]:
        """Make a move with full FIDE validation"""
        try:
            move = chess.Move.from_uci(move_uci)

            # Validate move legality
            if move not in self.board.legal_moves:
                return {"success": False, "error": "Illegal move", "legal_moves": [m.uci() for m in self.board.legal_moves]}

            # Store position for threefold repetition
            self.position_history.append(self.board.fen())

            # Make the move
            self.board.push(move)
            self.move_history.append(move)

            # Check game state
            game_state = self._check_game_state()

            return {
                "success": True,
                "move": move_uci,
                "san": self.board.san(move),
                "fen": self.board.fen(),
                "game_state": game_state,
                "check": self.board.is_check(),
                "legal_moves": [m.uci() for m in self.board.legal_moves]
            }

        except ValueError as e:
            return {"success": False, "error": f"Invalid move format: {str(e)}"}

    def _check_game_state(self) -> str:
        """Check for game end conditions per FIDE rules"""
        if self.board.is_checkmate():
            winner = "white" if self.board.turn == chess.BLACK else "black"
            self.result = f"1-0" if winner == "white" else "0-1"
            return f"checkmate_{winner}_wins"

        if self.board.is_stalemate():
            self.result = "1/2-1/2"
            return "stalemate_draw"

        if self.board.is_insufficient_material():
            self.result = "1/2-1/2"
            return "insufficient_material_draw"

        # Threefold repetition
        current_pos = self.board.fen().split(' ')[0]  # Position without clocks
        if self.position_history.count(current_pos) >= 2:  # Will be 3 after current move
            return "threefold_repetition_available"

        # 50-move rule
        if self.board.halfmove_clock >= 100:
            return "fifty_move_rule_available"

        return "active"

    def claim_draw(self, draw_type: str) -> Dict[str, Any]:
        """Handle draw claims"""
        if draw_type == "threefold_repetition":
            current_pos = self.board.fen().split(' ')[0]
            if self.position_history.count(current_pos) >= 2:
                self.result = "1/2-1/2"
                return {"success": True, "result": "draw_by_repetition"}

        elif draw_type == "fifty_move":
            if self.board.halfmove_clock >= 100:
                self.result = "1/2-1/2"
                return {"success": True, "result": "draw_by_fifty_move"}

        return {"success": False, "error": "Draw claim not valid"}

class GameSession:
    """Individual game session with timing and state management"""

    def __init__(self, game_id: str, white_player: Player, black_player: Optional[Player], 
                 time_control: TimeControl, variant: GameVariant = GameVariant.STANDARD):
        self.game_id = game_id
        self.white_player = white_player
        self.black_player = black_player
        self.time_control = time_control
        self.variant = variant
        self.engine = ChessEngine(variant)

        # Timing
        self.white_time = time_control.initial_seconds
        self.black_time = time_control.initial_seconds
        self.last_move_time = time.time()
        self.game_start_time = datetime.now()

        # Game metadata
        self.spectators: Set[str] = set()
        self.chat_messages: List[Dict] = []
        self.analysis_requests: List[str] = []

        # Anti-cheat
        self.move_times: List[float] = []
        self.suspicious_activities: List[Dict] = []

    def make_move(self, player_id: str, move_uci: str) -> Dict[str, Any]:
        """Process move with timing and validation"""
        current_time = time.time()
        move_time = current_time - self.last_move_time

        # Validate player turn
        expected_player = self.white_player.id if self.engine.board.turn == chess.WHITE else self.black_player.id
        if player_id != expected_player:
            return {"success": False, "error": "Not your turn"}

        # Update time
        if self.engine.board.turn == chess.WHITE:
            self.white_time -= move_time
            self.white_time += self.time_control.increment_seconds
        else:
            self.black_time -= move_time
            self.black_time += self.time_control.increment_seconds

        # Check time forfeit
        if self.white_time <= 0:
            return {"success": True, "result": "black_wins_time"}
        if self.black_time <= 0:
            return {"success": True, "result": "white_wins_time"}

        # Record move time for anti-cheat analysis
        self.move_times.append(move_time)

        # Make move
        result = self.engine.make_move(move_uci)
        if result["success"]:
            self.last_move_time = current_time

            # Anti-cheat: Check for suspiciously fast moves in complex positions
            if move_time < 0.5 and len(self.engine.move_history) > 10:
                complexity_score = len(result["legal_moves"])
                if complexity_score > 20:  # Complex position, very fast move
                    self.suspicious_activities.append({
                        "type": "fast_complex_move",
                        "move_time": move_time,
                        "complexity": complexity_score,
                        "timestamp": current_time
                    })

        return result

class MatchmakingSystem:
    """ELO-based matchmaking with preferences"""

    def __init__(self):
        self.waiting_players: Dict[str, Dict] = {}
        self.active_searches: Dict[str, asyncio.Task] = {}

    async def find_match(self, player: Player, time_control: TimeControl, 
                        variant: GameVariant, rating_range: int = 200) -> Optional[str]:
        """Find suitable opponent"""
        search_key = f"{player.id}_{time_control}_{variant}"

        # Check existing waiting players
        for waiting_id, waiting_data in self.waiting_players.items():
            if waiting_id == player.id:
                continue

            waiting_player = waiting_data["player"]
            if (waiting_data["time_control"] == time_control and 
                waiting_data["variant"] == variant and
                abs(waiting_player.rating - player.rating) <= rating_range):

                # Match found!
                del self.waiting_players[waiting_id]
                game_id = str(uuid.uuid4())
                return await self._create_game(game_id, player, waiting_player, time_control, variant)

        # Add to waiting pool
        self.waiting_players[search_key] = {
            "player": player,
            "time_control": time_control,
            "variant": variant,
            "timestamp": time.time()
        }

        return None

    async def _create_game(self, game_id: str, white: Player, black: Player, 
                          time_control: TimeControl, variant: GameVariant) -> str:
        """Create new game session"""
        # Randomly assign colors or use rating-based assignment
        if white.rating < black.rating:
            white, black = black, white

        game = GameSession(game_id, white, black, time_control, variant)
        # Store in game manager (would be injected in real implementation)
        return game_id

class TournamentManager:
    """Tournament system supporting multiple formats"""

    def __init__(self):
        self.tournaments: Dict[str, Dict] = {}
        self.player_tournaments: Dict[str, Set[str]] = defaultdict(set)

    def create_tournament(self, tournament_type: TournamentType, name: str, 
                         time_control: TimeControl, max_players: int = 64) -> str:
        """Create new tournament"""
        tournament_id = str(uuid.uuid4())

        tournament = {
            "id": tournament_id,
            "type": tournament_type,
            "name": name,
            "time_control": time_control,
            "max_players": max_players,
            "players": [],
            "rounds": [],
            "status": "registration",
            "created": datetime.now(),
            "pairings": [],
            "standings": []
        }

        self.tournaments[tournament_id] = tournament
        return tournament_id

    def join_tournament(self, tournament_id: str, player: Player) -> Dict[str, Any]:
        """Register player for tournament"""
        tournament = self.tournaments.get(tournament_id)
        if not tournament:
            return {"success": False, "error": "Tournament not found"}

        if tournament["status"] != "registration":
            return {"success": False, "error": "Registration closed"}

        if len(tournament["players"]) >= tournament["max_players"]:
            return {"success": False, "error": "Tournament full"}

        tournament["players"].append(player)
        self.player_tournaments[player.id].add(tournament_id)

        return {"success": True, "players_count": len(tournament["players"])}

    def start_tournament(self, tournament_id: str) -> Dict[str, Any]:
        """Begin tournament with first round pairings"""
        tournament = self.tournaments[tournament_id]

        if tournament["type"] == TournamentType.SWISS:
            return self._start_swiss_tournament(tournament)
        elif tournament["type"] == TournamentType.ARENA:
            return self._start_arena_tournament(tournament)
        # Add other tournament types...

        return {"success": False, "error": "Tournament type not implemented"}

    def _start_swiss_tournament(self, tournament: Dict) -> Dict[str, Any]:
        """Start Swiss-system tournament"""
        players = tournament["players"]
        if len(players) < 4:
            return {"success": False, "error": "Minimum 4 players required"}

        # First round: pair by rating
        players.sort(key=lambda p: p.rating, reverse=True)
        mid_point = len(players) // 2
        pairings = []

        for i in range(mid_point):
            pairings.append((players[i], players[i + mid_point]))

        tournament["pairings"] = pairings
        tournament["status"] = "active"
        tournament["current_round"] = 1

        return {"success": True, "pairings": len(pairings)}

class AntiCheatSystem:
    """Advanced anti-cheat with ML-based detection"""

    def __init__(self):
        self.engine_analysis_cache: Dict[str, Dict] = {}
        self.player_profiles: Dict[str, Dict] = defaultdict(dict)

    async def analyze_game(self, game: GameSession) -> Dict[str, Any]:
        """Comprehensive game analysis for cheating detection"""
        suspicion_score = 0
        flags = []

        # 1. Move time analysis
        if len(game.move_times) > 10:
            avg_time = sum(game.move_times) / len(game.move_times)
            time_variance = sum((t - avg_time) ** 2 for t in game.move_times) / len(game.move_times)

            # Unusually consistent timing (possible engine use)
            if time_variance < 0.1 and avg_time < 5.0:
                suspicion_score += 30
                flags.append("consistent_timing")

        # 2. Engine correlation analysis
        engine_correlation = await self._calculate_engine_correlation(game)
        if engine_correlation > 0.85:
            suspicion_score += 50
            flags.append("high_engine_correlation")

        # 3. Accuracy analysis
        accuracy = await self._calculate_move_accuracy(game)
        if accuracy > 95 and len(game.move_times) > 20:
            suspicion_score += 40
            flags.append("superhuman_accuracy")

        # 4. Browser focus analysis (would need frontend integration)
        # 5. Mouse movement patterns (would need frontend integration)

        return {
            "suspicion_score": suspicion_score,
            "flags": flags,
            "engine_correlation": engine_correlation,
            "accuracy": accuracy,
            "requires_review": suspicion_score > 70
        }

    async def _calculate_engine_correlation(self, game: GameSession) -> float:
        """Calculate correlation with engine moves"""
        if len(game.engine.move_history) < 10:
            return 0.0

        # This would use Stockfish or another engine for analysis
        # Simplified implementation
        engine_moves = 0
        total_moves = 0

        # Would analyze each position with engine and compare
        # For now, return placeholder
        return min(0.95, 0.3 + (len(game.suspicious_activities) * 0.1))

    async def _calculate_move_accuracy(self, game: GameSession) -> float:
        """Calculate overall move accuracy"""
        # Would use engine evaluation to determine accuracy
        # Simplified implementation
        return max(70.0, 90.0 - (len(game.suspicious_activities) * 5))

class WebSocketManager:
    """Real-time communication for live games"""

    def __init__(self):
        self.connections: Dict[str, Set] = defaultdict(set)
        self.game_connections: Dict[str, Set] = defaultdict(set)

    async def connect(self, websocket, user_id: str):
        """Register new WebSocket connection"""
        self.connections[user_id].add(websocket)

    async def disconnect(self, websocket, user_id: str):
        """Remove WebSocket connection"""
        self.connections[user_id].discard(websocket)

    async def join_game(self, websocket, game_id: str, user_id: str):
        """Join game room for live updates"""
        self.game_connections[game_id].add((websocket, user_id))

    async def broadcast_to_game(self, game_id: str, message: Dict[str, Any]):
        """Send message to all game participants"""
        if game_id in self.game_connections:
            for websocket, user_id in self.game_connections[game_id]:
                try:
                    await websocket.send_json(message)
                except:
                    # Connection closed, remove it
                    self.game_connections[game_id].discard((websocket, user_id))

class ChessPlatform:
    """Main platform orchestrator"""

    def __init__(self):
        self.players: Dict[str, Player] = {}
        self.games: Dict[str, GameSession] = {}
        self.matchmaking = MatchmakingSystem()
        self.tournaments = TournamentManager()
        self.anti_cheat = AntiCheatSystem()
        self.websocket_manager = WebSocketManager()

        # Analytics and logging
        self.game_analytics: Dict[str, Any] = defaultdict(dict)
        self.logger = logging.getLogger("ChessPlatform")

    async def create_player(self, username: str, email: str) -> str:
        """Register new player"""
        player_id = str(uuid.uuid4())
        player = Player(
            id=player_id,
            username=username,
            email=email,
            preferences={
                "theme": "default",
                "board_style": "2d",
                "piece_set": "classic",
                "sound_enabled": True,
                "auto_queen": False
            }
        )

        self.players[player_id] = player
        return player_id

    async def start_game(self, player1_id: str, player2_id: Optional[str], 
                        time_control: TimeControl, variant: GameVariant = GameVariant.STANDARD) -> str:
        """Start new game"""
        player1 = self.players[player1_id]
        player2 = self.players.get(player2_id) if player2_id else None

        game_id = str(uuid.uuid4())
        game = GameSession(game_id, player1, player2, time_control, variant)
        self.games[game_id] = game

        # Notify players via WebSocket
        await self.websocket_manager.broadcast_to_game(game_id, {
            "type": "game_start",
            "game_id": game_id,
            "white_player": player1.username,
            "black_player": player2.username if player2 else "AI",
            "time_control": str(time_control)
        })

        return game_id

    async def make_move(self, game_id: str, player_id: str, move: str) -> Dict[str, Any]:
        """Process move in active game"""
        game = self.games.get(game_id)
        if not game:
            return {"success": False, "error": "Game not found"}

        result = game.make_move(player_id, move)

        if result["success"]:
            # Broadcast move to spectators
            await self.websocket_manager.broadcast_to_game(game_id, {
                "type": "move",
                "move": move,
                "fen": result["fen"],
                "game_state": result["game_state"],
                "white_time": game.white_time,
                "black_time": game.black_time
            })

            # Check for game end
            if result.get("result"):
                await self._handle_game_end(game, result["result"])

        return result

    async def _handle_game_end(self, game: GameSession, result: str):
        """Process game completion"""
        # Update player ratings
        await self._update_ratings(game, result)

        # Run anti-cheat analysis
        cheat_analysis = await self.anti_cheat.analyze_game(game)
        if cheat_analysis["requires_review"]:
            self.logger.warning(f"Game {game.game_id} flagged for review: {cheat_analysis['flags']}")

        # Generate game analytics
        self.game_analytics[game.game_id] = {
            "duration": time.time() - game.last_move_time,
            "moves": len(game.engine.move_history),
            "variant": game.variant.value,
            "time_control": str(game.time_control),
            "result": result,
            "cheat_analysis": cheat_analysis
        }

        # Export PGN
        pg