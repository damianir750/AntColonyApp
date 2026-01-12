import tkinter as tk
from tkinter import ttk, messagebox, simpledialog, filedialog, scrolledtext
from PIL import Image, ImageTk, ImageDraw
import os
import json
import calendar
from datetime import datetime, timedelta
from tkcalendar import DateEntry
import threading
import time
import shutil
import smtplib
import ssl
import logging
import urllib.request
import re

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    datefmt='%H:%M:%S'
)
logger = logging.getLogger(__name__)

try:
    from plyer import notification
    NOTIFICATIONS_AVAILABLE = True
except ImportError:
    NOTIFICATIONS_AVAILABLE = False
    logger.warning("Per le notifiche installa: pip install plyer")

try:
    from pystray import MenuItem as item, Menu
    from pystray import Icon as TrayIcon
    PYSTRAY_AVAILABLE = True
except ImportError:
    PYSTRAY_AVAILABLE = False
    logger.warning("Per la riduzione a icona nella barra di sistema installa: pip install pystray")

# --- Costanti ---
# Get the directory where this script is located
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))

DATA_FILE = os.path.join(SCRIPT_DIR, "colonies.json")
IMAGE_DIR = os.path.join(SCRIPT_DIR, "colony_images")
BACKUP_DIR = os.path.join(SCRIPT_DIR, "backups")
DEFAULT_BG_COLOR = "#1a233b"  # Blu scuro
CARD_BG_COLOR = "#212e4d"   # Blu più chiaro per i pannelli
TEXT_COLOR = "#ecf0f1"
ACCENT_COLOR = "#3498db"
GRAPH_COLOR = "#2ecc71" # Verde per il grafico
CURRENT_VERSION = "1.2.1"

# --- Database Specie ---
SPECIES_DATA = {
    "Messor barbarus": {
        "description": "Formica mietitrice. Granivora, necessita di semi.",
        "notes": "Temp: 22-26°C. Umidità: 50-70%. Ibernazione: Sì (Nov-Mar, 15°C).\nCibo: Semi (90%), insetti morti (10%).\nRegina sciauma in autunno."
    },
    "Lasius niger": {
        "description": "Formica nera da giardino. Facile da allevare.",
        "notes": "Temp: 20-25°C. Umidità: 30-50%. Ibernazione: Sì (Nov-Mar, 5-10°C).\nCibo: Insetti morti, liquidi zuccherini.\nMolto resistente."
    },
    "Lasius flavus": {
        "description": "Formica gialla sotterranea. Timida.",
        "notes": "Temp: 20-24°C. Umidità: 50-70%. Ibernazione: Sì.\nCibo: Piccoli insetti, liquidi.\nVive nel sottosuolo, evitare luce forte."
    },
    "Camponotus vagus": {
        "description": "Formica carpentiere. Grande e aggressiva.",
        "notes": "Temp: 24-28°C. Umidità: 40-60%. Ibernazione: Sì (corta).\nCibo: Insetti, liquidi zuccherini.\nNidifica nel legno secco."
    },
    "Camponotus ligniperda": {
        "description": "Una delle formiche più grandi d'Europa.",
        "notes": "Temp: 21-25°C. Umidità: 50%. Ibernazione: Obbligatoria (lunga).\nCibo: Liquidi zuccherini, insetti.\nSviluppo lento."
    },
    "Pheidole pallidula": {
        "description": "Piccola formica con soldati macrocefali.",
        "notes": "Temp: 25-28°C. Umidità: 50-60%. Ibernazione: Breve/Facoltativa.\nCibo: Insetti (molto voraci), semi, liquidi.\nAttenzione alle fughe!"
    },
    "Crematogaster scutellaris": {
        "description": "Formica rizzaculo. Testa rossa, addome a punta.",
        "notes": "Temp: 22-28°C. Umidità: Bassa (nidifica nel legno).\nIbernazione: Breve (10-15°C).\nCibo: Liquidi zuccherini, insetti."
    },
    "Messor capitatus": {
        "description": "Formica mietitrice nera grande.",
        "notes": "Simile a barbarus ma tutta nera.\nTemp: 24-28°C. Cibo: Prevalentemente semi."
    },
    "Tetramorium caespitum": {
        "description": "Formica piccola e combattiva.",
        "notes": "Temp: 21-26°C. Onnivora, mangia tutto. Crescita esplosiva."
    }
}


DEFAULT_UPDATE_URL = "https://raw.githubusercontent.com/damianir750/AntColonyApp/refs/heads/main/app%20formiche.py"


class AntColonyApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Ant Colony Monitor")
        self.root.geometry("1400x900")
        self.root.configure(bg=DEFAULT_BG_COLOR)
        self.root.minsize(1000, 700)

        # Configurazione dello stile moderno
        self.style = ttk.Style()
        self.style.theme_use('clam')
        self._configure_styles()

        self.settings = {}
        self.colonies = []
        self.custom_species = {}
        self.current_view_mode = "grid" # "grid" or "dashboard"
        
        self.colonies, self.settings, self.custom_species = self.load_data()
        
        # Merge DB
        self.species_db = SPECIES_DATA.copy()
        self.species_db.update(self.custom_species)
        
        if os.path.exists(DATA_FILE):
            self.create_backup(silent=True)

        self.current_colony = None
        self.current_filtered_colonies = None
        self.current_calendar_date = datetime.now()
        self.last_size = (0, 0)
        self.last_colony_grid_width = 0
        
        # Auto-check updates
        threading.Thread(target=self.check_for_updates, kwargs={'silent': True}, daemon=True).start()

        # Gestione dell'immagine di sfondo
        self._current_background_label = None
        self._current_background_photo = None
        self.background_image_path = self.settings.get("background_image_path")
        self.update_background_image()
        self.root.bind("<Configure>", self.on_window_resize)

        # Avvia il thread per il controllo delle notifiche
        self.notification_thread_running = False
        self.start_notification_thread()
        
        self._is_drawing = False # Recursion guard
        self.create_main_frame()
        self.center_window()

    @property
    def bg_color(self):
        """Restituisce il colore di sfondo: trasparente se c'è un'immagine, altrimenti il default."""
        return DEFAULT_BG_COLOR # Reverted transparency


    def load_data(self):
        colonies = []
        colonies = []
        custom_species = {}
        settings = {
            "notifications": True,
            "notifications_email": False,
            "update_url": DEFAULT_UPDATE_URL, # URL per l'aggiornamento

            "notifications_desktop": True,
            "email_sender": "",
            "email_password": "",
            "email_recipient": "",
            "smtp_server": "smtp.gmail.com",
            "smtp_port": 587,
            "theme": "dark",
            "background_image_path": None,
        }
        if os.path.exists(DATA_FILE):
            try:
                with open(DATA_FILE, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                    colonies = data.get("colonies", [])
                    custom_species = data.get("custom_species", {})
                    settings.update(data.get("settings", {}))
                    
                    # Fix for update_url: overwrite if it's the old incorrect one
                    old_url = "https://raw.githubusercontent.com/damianir750/AntColonyApp/main/app%20formiche.py"
                    if settings.get("update_url") == old_url:
                        settings["update_url"] = DEFAULT_UPDATE_URL
                    
                    # Logica di migrazione per i vecchi formati di dati
                    for colony in colonies:
                        # Migrazione del campo population in history
                        if "population" in colony and "history" not in colony:
                            try:
                                pop = int(colony["population"])
                                colony["history"] = [{
                                    "timestamp": datetime.now().isoformat(),
                                    "population": pop,
                                    "mortalita": 0,
                                    "presenza_uova_larve": "non registrato",
                                    "stato_salute_generale": "non registrato"
                                }]
                            except ValueError:
                                colony["history"] = []
                            del colony["population"]
                        elif "history" not in colony:
                            colony["history"] = []
                            
                        # Migrazione del campo feeding_schedule
                        if "feeding_schedule" in colony:
                            new_schedule = []
                            for item in colony["feeding_schedule"]:
                                if isinstance(item, str):
                                    new_schedule.append({"datetime": item, "description": "", "food_type": "", "quantity": ""})
                                else:
                                    # Aggiungi i nuovi campi se non esistono
                                    item.setdefault("food_type", "")
                                    item.setdefault("quantity", "")
                                    item.setdefault("description", "")
                                    new_schedule.append(item)
                            colony["feeding_schedule"] = new_schedule
                        
                        # Inizializza i nuovi campi se non esistono
                        colony.setdefault("recurring_schedule", [])
                        colony.setdefault("feeding_history", [])
                        colony.setdefault("notes", "")

            except (json.JSONDecodeError, FileNotFoundError):
                messagebox.showerror("Errore", "Impossibile caricare il file dei dati. Verrà creato un nuovo file.")
                colonies = []
                
            except (json.JSONDecodeError, FileNotFoundError):
                messagebox.showerror("Errore", "Impossibile caricare il file dei dati. Verrà creato un nuovo file.")
                colonies = []
                
        return colonies, settings, custom_species

    def save_data(self):
        try:
            with open(DATA_FILE, 'w', encoding='utf-8') as f:
                data = {
                    "colonies": self.colonies,
                    "settings": self.settings,
                    "custom_species": self.custom_species
                }
                json.dump(data, f, indent=2, ensure_ascii=False)
        except Exception as e:
            messagebox.showerror("Errore", f"Impossibile salvare i dati: {e}")

    def center_window(self):
        self.root.update_idletasks()
        width = self.root.winfo_width()
        height = self.root.winfo_height()
        x = (self.root.winfo_screenwidth() // 2) - (width // 2)
        y = (self.root.winfo_screenheight() // 2) - (height // 2)
        self.root.geometry(f'{width}x{height}+{x}+{y}')

    def _configure_styles(self):
        self.style.configure("Header.TLabel",
                           font=("Segoe UI", 18, "bold"),
                           foreground=TEXT_COLOR,
                           background=DEFAULT_BG_COLOR)

        self.style.configure("Card.TFrame",
                           background=CARD_BG_COLOR,
                           relief="raised",
                           borderwidth=2)

        self.style.configure("Modern.TButton",
                           font=("Segoe UI", 10, "bold"),
                           foreground=TEXT_COLOR,
                           background=ACCENT_COLOR,
                           borderwidth=0)

        self.style.configure("Danger.TButton",
                           font=("Segoe UI", 10, "bold"),
                           foreground=TEXT_COLOR,
                           background="#e74c3c",
                           borderwidth=0)

        self.style.configure("Success.TButton",
                           font=("Segoe UI", 10, "bold"),
                           foreground=TEXT_COLOR,
                           background="#27ae60",
                           borderwidth=0)
        
        self.style.configure("Warning.TButton",
                           font=("Segoe UI", 10, "bold"),
                           foreground=TEXT_COLOR,
                           background="#f39c12",
                           borderwidth=0)
        
        self.style.map("Modern.TButton", 
                       background=[('active', '#5d9cec')])
        self.style.map("Danger.TButton", 
                       background=[('active', '#e86a5e')])
        self.style.map("Success.TButton", 
                       background=[('active', '#3fbf71')])
        self.style.map("Warning.TButton", 
                       background=[('active', '#f5b550')])

        # Nuovo stile per le schede del Notebook
        self.style.configure("TNotebook", background=DEFAULT_BG_COLOR, borderwidth=0)
        self.style.configure("TNotebook.Tab", background=CARD_BG_COLOR, foreground=TEXT_COLOR)
        self.style.map("TNotebook.Tab", background=[("selected", ACCENT_COLOR)], foreground=[("selected", "#ffffff")])


        
    def create_main_frame(self):
        self.clear_frame()
        self.current_colony = None # Resetta la colonia attuale

        main_container = tk.Frame(self.root, bg=self.bg_color)
        main_container.pack(fill="both", expand=True)

        self._create_main_header(main_container)

        # Container principale per i contenuti scambiabili
        self.content_container = tk.Frame(main_container, bg=self.bg_color)
        self.content_container.pack(fill="both", expand=True, padx=20, pady=20)

        # -- Vista Griglia (Canvas + Scrollbar) --
        self.grid_container = tk.Frame(self.content_container, bg=DEFAULT_BG_COLOR)
        
        # --- barra dei Filtri ---
        self.filter_frame = tk.Frame(self.grid_container, bg=CARD_BG_COLOR, padx=10, pady=10)
        self.filter_frame.pack(side="top", fill="x", pady=(0, 10))
        
        # Row 1: Search & Species
        f_row1 = tk.Frame(self.filter_frame, bg=CARD_BG_COLOR)
        f_row1.pack(fill="x", pady=2)
        
        tk.Label(f_row1, text="🔍 Cerca:", font=("Segoe UI", 10), bg=CARD_BG_COLOR, fg=TEXT_COLOR).pack(side="left")
        self.filter_name_var = tk.StringVar()
        self.filter_name_var.trace("w", lambda name, index, mode: self.apply_filters())
        
        e_search = tk.Entry(f_row1, textvariable=self.filter_name_var, width=20, font=("Segoe UI", 10),
                           bg=DEFAULT_BG_COLOR, fg=TEXT_COLOR, relief="flat", insertbackground=TEXT_COLOR)
        e_search.pack(side="left", padx=5, ipady=3)
        
        tk.Label(f_row1, text="🐜 Specie:", font=("Segoe UI", 10), bg=CARD_BG_COLOR, fg=TEXT_COLOR).pack(side="left", padx=(15, 5))
        self.filter_species_var = tk.StringVar()
        species_values = ["Tutte"] + sorted(list(self.species_db.keys()))
        f_species = ttk.Combobox(f_row1, textvariable=self.filter_species_var, values=species_values, state="readonly", width=20)
        f_species.current(0)
        f_species.pack(side="left")
        f_species.bind("<<ComboboxSelected>>", lambda e: self.apply_filters())
        
        # Row 2: Pop Range & Reset
        f_row2 = tk.Frame(self.filter_frame, bg=CARD_BG_COLOR)
        f_row2.pack(fill="x", pady=2)
        
        tk.Label(f_row2, text="👥 Popolazione:", font=("Segoe UI", 10), bg=CARD_BG_COLOR, fg=TEXT_COLOR).pack(side="left")
        self.filter_pop_min_var = tk.StringVar()
        self.filter_pop_max_var = tk.StringVar()
        
        # Helper to trigger filter on enter or focus out
        def on_pop_change(e): self.apply_filters()
        
        e_min = tk.Entry(f_row2, textvariable=self.filter_pop_min_var, width=8, font=("Segoe UI", 10),
                        bg=DEFAULT_BG_COLOR, fg=TEXT_COLOR, relief="flat", insertbackground=TEXT_COLOR)
        e_min.pack(side="left", padx=5, ipady=3)
        e_min.bind("<Return>", on_pop_change)
        e_min.bind("<FocusOut>", on_pop_change)
        
        tk.Label(f_row2, text="-", bg=CARD_BG_COLOR, fg=TEXT_COLOR).pack(side="left")
        
        e_max = tk.Entry(f_row2, textvariable=self.filter_pop_max_var, width=8, font=("Segoe UI", 10),
                        bg=DEFAULT_BG_COLOR, fg=TEXT_COLOR, relief="flat", insertbackground=TEXT_COLOR)
        e_max.pack(side="left", padx=5, ipady=3)
        e_max.bind("<Return>", on_pop_change)
        e_max.bind("<FocusOut>", on_pop_change)

        ttk.Button(f_row2, text="❌ Reset", style="Modern.TButton", command=self.reset_filters).pack(side="left", padx=15)
        ttk.Button(f_row2, text="✅ Applica", style="Success.TButton", command=self.apply_filters).pack(side="left", padx=5)

        self.canvas = tk.Canvas(self.grid_container, bg=DEFAULT_BG_COLOR, highlightthickness=0)
        self.scrollbar = ttk.Scrollbar(self.grid_container, orient="vertical", command=self.canvas.yview)
        
        self.canvas.configure(yscrollcommand=self.scrollbar.set)
        self.canvas.bind("<MouseWheel>", self._on_mousewheel)
        self.canvas.bind("<Configure>", self.on_canvas_configure)

        self.canvas.pack(side="left", fill="both", expand=True)
        self.scrollbar.pack(side="right", fill="y")

        # -- Vista Dashboard --
        self.dashboard_container = tk.Frame(self.content_container, bg=DEFAULT_BG_COLOR)

        # Inizializza la vista corretta
        self.update_view()

    def update_view(self):
        """Switch between Grid and Dashboard views."""
        # Nascondi tutto
        self.grid_container.pack_forget()
        self.dashboard_container.pack_forget()
        
        if self.current_view_mode == "grid":
            if not self.colonies:
                self._show_empty_state()
            else:
                self.grid_container.pack(fill="both", expand=True)
                self.display_colonies()
        else:
            self.dashboard_container.pack(fill="both", expand=True)
            self.show_dashboard()

    def toggle_view_mode(self, mode):
        self.current_view_mode = mode
        self.update_view()

    def _show_empty_state(self):
        # Mostra stato vuoto (solo se siamo in grid mode e non abbiamo colonie)
        # Puliamo grid container per mostrare empty frame
        for widget in self.grid_container.winfo_children():
            if widget not in (self.canvas, self.scrollbar):
                widget.destroy()

        if self.colonies:
            return

        # Nascondi canvas/scroll
        self.canvas.pack_forget()
        self.scrollbar.pack_forget()
        
        empty_frame = tk.Frame(self.grid_container, bg=self.bg_color)
        empty_frame.pack(expand=True, fill="both")

        empty_label = tk.Label(empty_frame,
                             text="🔍 Nessuna colonia registrata\n\nClicca su 'Nuova Colonia' per iniziare!",
                             font=("Segoe UI", 16),
                             fg="#95a5a6",
                             bg=self.bg_color,
                             justify="center")
        empty_label.pack(expand=True)
        
        self.grid_container.pack(fill="both", expand=True)
        
        # Bind scroll events to keep background fixed
        self.scrollbar.bind("<B1-Motion>", lambda e: self._update_bg_position())

        self.display_colonies()
        
    def on_canvas_configure(self, event):
        # Prevent "jitter"/stuttering during window move:
        # Only react if dimensions actually changed.
        
        current_width = event.width
        current_height = event.height
        
        if not hasattr(self, 'last_canvas_width'):
            self.last_canvas_width = current_width
            self.last_canvas_height = current_height
            return

        # Check if size changed (ignore position changes)
        if (abs(self.last_canvas_width - current_width) < 2 and 
            abs(self.last_canvas_height - current_height) < 2):
            return

        # Debounce: Cancel any pending redraw
        if hasattr(self, '_resize_after_id') and self._resize_after_id:
            self.root.after_cancel(self._resize_after_id)
        
        # Schedule redraw
        self._resize_after_id = self.root.after(100, self._do_resize_redraw, current_width, current_height)


    def _do_resize_redraw(self, new_width, new_height):
        """Perform the actual resize redraw after debounce delay."""
        self._resize_after_id = None
        self.last_canvas_width = new_width
        self.last_canvas_height = new_height
        self._update_bg_position() # Update bg on resize
        self.display_colonies()

    def _on_mousewheel(self, event):
        self.canvas.yview_scroll(int(-1*(event.delta/120)), "units")
        self._update_bg_position()
    
    def _update_bg_position(self):
        """Keep background image fixed in viewport when scrolling."""
        if not hasattr(self, 'canvas') or not self.canvas.winfo_exists():
            return
        bg_items = self.canvas.find_withtag("bg")
        if bg_items:
            canvas_width = self.canvas.winfo_width()
            canvas_height = self.canvas.winfo_height()
            # Get scroll offset
            y_scroll = self.canvas.yview()[0]
            scroll_region = self.canvas.cget('scrollregion')
            if scroll_region:
                try:
                    _, _, _, total_h = map(float, scroll_region.split())
                    y_offset = y_scroll * total_h
                except:
                    y_offset = 0
            else:
                y_offset = 0
            x_center = canvas_width // 2
            y_center = (canvas_height // 2) + y_offset
            self.canvas.coords(bg_items[0], x_center, y_center)

    def _create_main_header(self, parent_frame):
        header = tk.Frame(parent_frame, bg=CARD_BG_COLOR, height=80)
        header.pack(fill="x", padx=0, pady=0)
        header.pack_propagate(False)

        header_content = tk.Frame(header, bg=CARD_BG_COLOR)
        header_content.pack(fill="both", expand=True, padx=20, pady=15)

        title_label = tk.Label(header_content,
                              text="🐜 Ant Colony Monitor",
                              font=("Segoe UI", 20, "bold"),
                              fg=TEXT_COLOR,
                              bg=CARD_BG_COLOR)
        title_label.pack(side="left")
        
        # View Switcher (Centro-Sinistra)
        view_frame = tk.Frame(header_content, bg=CARD_BG_COLOR)
        view_frame.pack(side="left", padx=40)
        
        ttk.Button(view_frame, text="🔲 Quadri", style="Modern.TButton",
                  command=lambda: self.toggle_view_mode("grid")).pack(side="left", padx=2)
        ttk.Button(view_frame, text="📊 Dashboard", style="Modern.TButton",
                  command=lambda: self.toggle_view_mode("dashboard")).pack(side="left", padx=2)

        btn_frame = tk.Frame(header_content, bg=CARD_BG_COLOR)
        btn_frame.pack(side="right")

        ttk.Button(btn_frame, text="📅 Calendario",
                  style="Modern.TButton",
                  command=self.show_calendar).pack(side="right", padx=5)

        ttk.Button(btn_frame, text="⚙️ Impostazioni",
                  style="Modern.TButton",
                  command=self.show_settings).pack(side="right", padx=5)

        ttk.Button(btn_frame, text="🖼️ Sfondo",
                  style="Modern.TButton",
                  command=self.set_background_image).pack(side="right", padx=5)

        ttk.Button(btn_frame, text="📥 Importa",
                  style="Modern.TButton",
                  command=self.import_colony).pack(side="right", padx=5)

        ttk.Button(btn_frame, text="➕ Nuova Colonia",
                  style="Success.TButton",
                  command=self.create_colony).pack(side="right", padx=5)

    def reset_filters(self):
        self.filter_name_var.set("")
        self.filter_species_var.set("Tutte")
        self.filter_pop_min_var.set("")
        self.filter_pop_max_var.set("")
        self.current_filtered_colonies = None
        self.display_colonies()

    def apply_filters(self, event=None):
        name_filter = self.filter_name_var.get().lower().strip()
        species_filter = self.filter_species_var.get()
        pop_min = self.filter_pop_min_var.get().strip()
        pop_max = self.filter_pop_max_var.get().strip()
        
        filtered = []
        for colony in self.colonies:
            # 1. Name Filter
            if name_filter and name_filter not in colony["name"].lower():
                continue
            
            # 2. Species Filter
            if species_filter != "Tutte":
                c_species = colony.get("species", "")
                if c_species != species_filter:
                    continue
            
            # 3. Population Filter
            current_pop = 0
            if colony.get("history"):
                current_pop = colony["history"][-1]["population"]
            
            try:
                if pop_min and current_pop < int(pop_min):
                    continue
            except ValueError:
                pass # Ignore invalid input
                
            try:
                if pop_max and current_pop > int(pop_max):
                    continue
            except ValueError:
                pass

            filtered.append(colony)
            
        self.current_filtered_colonies = filtered
        self.display_colonies(filtered)

    def display_colonies(self, colonies_list=None):
        if getattr(self, '_is_drawing', False):
            return
            
        self._is_drawing = True
        try:
            # Determine source list
            if colonies_list is None:
                colonies_list = self.current_filtered_colonies if self.current_filtered_colonies is not None else self.colonies
            
            # Check for smart reuse
            children = self.canvas.winfo_children()
            sorted_colonies = sorted(colonies_list, key=lambda x: x['name'].lower())
            
            # Draw/Update Background
            bg_drawn = False
            if self.background_image_path and os.path.exists(self.background_image_path):
                 self.draw_background_on_canvas()
                 bg_drawn = True
            else:
                 self.canvas.delete("bg") # Clear background if it exists

            # Configurazione griglia manuale
            canvas_width = self.canvas.winfo_width()
            if canvas_width <= 1: canvas_width = self.root.winfo_width() # Fallback
            
            # Padding
            PAD_X = 15
            PAD_Y = 15
            
            num_columns = max(1, canvas_width // 290)
            self.last_colony_grid_width = num_columns
            
            col_width = (canvas_width - (PAD_X * (num_columns + 1))) // num_columns
            
            current_x = PAD_X
            current_y = PAD_Y
            row_max_h = 0
            
            # Smart Reuse Logic
            if len(children) == len(sorted_colonies) and all(hasattr(c, 'canvas_id') for c in children):
                # Reuse existing widgets
                for idx, colony in enumerate(sorted_colonies):
                    col_idx = idx % num_columns
                    if col_idx == 0 and idx > 0:
                        current_x = PAD_X
                        current_y += row_max_h + PAD_Y
                        row_max_h = 0
                    
                    card = children[idx]
                    
                    # Force width update which might change height due to wrapping
                    # Need to update content frame width? width in create_window handles container size
                    # wrapper labels use col_width-40
                    
                    # Update wrapping on labels if needed
                    for child in card.winfo_children(): # card_content
                         for subchild in child.winfo_children(): # labels etc
                             if isinstance(subchild, tk.Label) and subchild.cget("wraplength") > 0:
                                 subchild.configure(wraplength=col_width-40)
                    
                    # Use reqheight without forcing immediate layout update
                    h = card.winfo_reqheight()
                    if h <= 1:  # Widget not yet realized
                        h = 250  # Default reasonable height
                    if h > row_max_h: row_max_h = h
                    
                    self.canvas.coords(card.canvas_id, current_x, current_y)
                    self.canvas.itemconfigure(card.canvas_id, width=col_width, height=h)
                    self.canvas.tag_raise(card.canvas_id) # Ensure above background
                    
                    current_x += col_width + PAD_X
            else:
                # Full Rebuild
                for widget in self.canvas.winfo_children():
                    widget.destroy()
                self.canvas.delete("all")
                
                # Redraw background after delete all
                if bg_drawn:
                    self.draw_background_on_canvas()

                for idx, colony in enumerate(sorted_colonies):
                    col_idx = idx % num_columns
                    if col_idx == 0 and idx > 0:
                        current_x = PAD_X
                        current_y += row_max_h + PAD_Y
                        row_max_h = 0
                    
                    card = tk.Frame(self.canvas, bg=CARD_BG_COLOR, relief="raised", bd=2, width=col_width)
                    
                    card_content = tk.Frame(card, bg=CARD_BG_COLOR)
                    card_content.pack(fill="both", expand=True, padx=20, pady=20)
    
                    img_frame = tk.Frame(card_content, bg=CARD_BG_COLOR)
                    img_frame.pack(pady=(0, 15))
                    self._create_colony_image_card(img_frame, colony)
    
                    name_label = tk.Label(card_content,
                                    text=colony["name"],
                                    font=("Segoe UI", 14, "bold"),
                                    fg=TEXT_COLOR,
                                    bg=CARD_BG_COLOR,
                                    wraplength=col_width-40)
                    name_label.pack(pady=(0, 2))
                
                    # Specie Label
                    if colony.get("species"):
                        tk.Label(card_content,
                                text=colony["species"],
                                font=("Segoe UI", 10, "italic"),
                                fg=ACCENT_COLOR,
                                bg=CARD_BG_COLOR).pack(pady=(0, 5))

                    date_text = f"📅 {colony['collection_date']}"
                    try:
                        collection_date_obj = datetime.strptime(colony['collection_date'], '%Y-%m-%d').date()
                        days_old = (datetime.now().date() - collection_date_obj).days
                        days_text = self.format_days(days_old)
                        date_text += f" ({days_text})"
                    except (ValueError, KeyError):
                        pass
    
                    date_label = tk.Label(card_content,
                                        text=date_text,
                                        font=("Segoe UI", 10),
                                        fg="#bdc3c7",
                                        bg=CARD_BG_COLOR)
                    date_label.pack(pady=2)
    
                    last_pop = "0"
                    if colony.get("history"):
                        last_pop = colony['history'][-1]['population']
                        
                    pop_label = tk.Label(card_content,
                                       text=f"👥 Popolazione: {last_pop}",
                                       font=("Segoe UI", 10),
                                       fg="#bdc3c7",
                                       bg=CARD_BG_COLOR)
                    pop_label.pack(pady=2)
    
                    description_preview = colony.get("description", "")
                    if description_preview:
                        desc_label = tk.Label(card_content,
                                              text=f"📝 {description_preview[:50]}{'...' if len(description_preview) > 50 else ''}",
                                              font=("Segoe UI", 9, "italic"),
                                              fg="#95a5a6",
                                              bg=CARD_BG_COLOR,
                                              wraplength=col_width-40)
                        desc_label.pack(pady=2)
    
                    btn_frame = tk.Frame(card_content, bg=CARD_BG_COLOR)
                    btn_frame.pack(pady=(15, 0))
    
                    ttk.Button(btn_frame, text="Apri",
                              style="Modern.TButton",
                              command=lambda c=colony: self.show_colony(c)).pack(side="left", padx=5)
    
                    ttk.Button(btn_frame, text="Elimina",
                              style="Danger.TButton",
                              command=lambda c=colony: self.delete_colony(c)).pack(side="left", padx=5)
                    
                    card.update_idletasks()
                    w = col_width
                    h = card.winfo_reqheight()
                    
                    item_id = self.canvas.create_window(current_x, current_y, window=card, anchor="nw", width=w, height=h, tags="card")
                    card.canvas_id = item_id # Store ID for reuse
                    
                    if h > row_max_h:
                        row_max_h = h
                        
                    current_x += col_width + PAD_X
            
            # Aggiorna scrollregion
            total_h = current_y + row_max_h + PAD_Y
            self.canvas.configure(scrollregion=(0, 0, canvas_width, total_h))
        finally:
            self._is_drawing = False
    
    def draw_background_on_canvas(self):
        if not self.background_image_path or not os.path.exists(self.background_image_path):
            return
            
        try:
            img = Image.open(self.background_image_path)
            canvas_width = self.canvas.winfo_width()
            canvas_height = self.canvas.winfo_height()
            
            if canvas_width <= 1: canvas_width = self.root.winfo_width()
            if canvas_height <= 1: canvas_height = self.root.winfo_height()
            
            # Ridimensiona immagine per coprire (cover) o contenere (contain)? 
            # Cover è meglio per sfondo
            if canvas_width > 0 and canvas_height > 0:
                img_ratio = img.width / img.height
                canvas_ratio = canvas_width / canvas_height
                
                if canvas_ratio > img_ratio:
                    new_width = canvas_width
                    new_height = int(canvas_width / img_ratio)
                else:
                    new_height = canvas_height
                    new_width = int(canvas_height * img_ratio)
                    
                img = img.resize((new_width, new_height), Image.Resampling.BILINEAR)
                self.bg_photo_canvas = ImageTk.PhotoImage(img) # Mantieni reference
                
                # Centra immagine
                x_center = canvas_width // 2
                y_center = canvas_height // 2
                
                # Cerca se esiste già
                bg_items = self.canvas.find_withtag("bg")
                
                # Calculate y position accounting for scroll offset
                y_scroll = self.canvas.yview()[0]
                scroll_region = self.canvas.cget('scrollregion')
                if scroll_region:
                    try:
                        _, _, _, total_h = map(float, scroll_region.split())
                        y_offset = y_scroll * total_h
                    except:
                        y_offset = 0
                else:
                    y_offset = 0
                    
                x_center = canvas_width // 2
                y_center = (canvas_height // 2) + y_offset
                
                if bg_items:
                    self.canvas.itemconfig(bg_items[0], image=self.bg_photo_canvas)
                    self.canvas.coords(bg_items[0], x_center, y_center)
                else:
                    self.canvas.create_image(x_center, y_center, image=self.bg_photo_canvas, tags="bg")
                    self.canvas.tag_lower("bg") # Invia in fondo
        except Exception as e:
            print(f"Error drawing background: {e}")

    
    def format_days(self, days):
        if days == 0:
            return "Oggi"
        elif days == 1:
            return "1 giorno"
        elif days < 30:
            return f"{days} giorni"
        elif days < 365:
            months = days // 30
            return f"{months} mesi"
        else:
            years = days // 365
            months = (days % 365) // 30
            return f"{years} anni, {months} mesi"

    def _create_colony_image_card(self, parent, colony):
        img_path = colony.get("profile_image", "")
        if img_path and os.path.exists(img_path):
            try:
                img = Image.open(img_path)
                img.thumbnail((180, 180), Image.Resampling.LANCZOS)
                photo = ImageTk.PhotoImage(img)

                img_label = tk.Label(parent, image=photo, bg=CARD_BG_COLOR)
                img_label.image = photo
                img_label.pack()
            except (IOError, OSError):
                self.create_placeholder_image(parent)
        else:
            self.create_placeholder_image(parent)

    def create_placeholder_image(self, parent):
        placeholder = tk.Label(parent,
                             text="🐜\nNessuna\nImmagine",
                             font=("Segoe UI", 12),
                             fg="#95a5a6",
                             bg=DEFAULT_BG_COLOR,
                             width=15,
                             height=8,
                             justify="center")
        placeholder.pack()
        
    def create_colony(self):
        dialog = tk.Toplevel(self.root)
        dialog.title("Nuova Colonia")
        dialog.geometry("500x700")
        dialog.configure(bg=CARD_BG_COLOR)
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.focus_set()

        dialog.geometry(f"+{self.root.winfo_rootx()+150}+{self.root.winfo_rooty()+50}")

        content = tk.Frame(dialog, bg=CARD_BG_COLOR)
        content.pack(fill="both", expand=True, padx=30, pady=30)

        tk.Label(content, text="Crea Nuova Colonia",
                font=("Segoe UI", 16, "bold"),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(pady=(0, 20))

        tk.Label(content, text="Nome della colonia:",
                font=("Segoe UI", 12),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", pady=(0, 5))

        name_var = tk.StringVar()
        name_entry = tk.Entry(content, textvariable=name_var,
                             font=("Segoe UI", 12),
                             width=30)
        name_entry.pack(fill="x", pady=(0, 5))
        name_entry.focus()
        
        # --- Sezione Specie ---
        tk.Label(content, text="Specie (Database):", font=("Segoe UI", 10), fg="#bdc3c7", bg=CARD_BG_COLOR).pack(anchor="w", pady=(10, 0))
        
        species_frame = tk.Frame(content, bg=CARD_BG_COLOR)
        species_frame.pack(fill="x", pady=(0, 5))
        
        species_var = tk.StringVar()
        # Ordina: prima le custom, poi le default
        all_species = sorted(list(self.species_db.keys()))
        species_combo = ttk.Combobox(species_frame, textvariable=species_var, values=all_species)
        species_combo.pack(side="left", fill="x", expand=True)
        
        def save_new_species():
            name = species_var.get().strip()
            notes = info_text.get("1.0", tk.END).strip()
            desc = description_text.get("1.0", tk.END).strip()
            
            if not name:
                messagebox.showerror("Errore", "Inserisci il nome della specie.")
                return
            if name in self.species_db and name not in self.custom_species:
                messagebox.showerror("Errore", "Non puoi sovrascrivere le specie predefinite.")
                return
            
            # Salva
            self.custom_species[name] = {"description": desc, "notes": notes}
            self.species_db[name] = self.custom_species[name]
            self.save_data()
            
            # Aggiorna combo
            species_combo['values'] = sorted(list(self.species_db.keys()))
            messagebox.showinfo("Successo", f"Specie '{name}' salvata nel database!")

        ttk.Button(species_frame, text="💾 Salva Specie", command=save_new_species, style="Modern.TButton").pack(side="left", padx=(5, 0))
        
        # Info Box Modificabile
        tk.Label(content, text="Info Cura / Note (Modificabile):", font=("Segoe UI", 10, "bold"), fg="#bdc3c7", bg=CARD_BG_COLOR).pack(anchor="w")
        info_text = scrolledtext.ScrolledText(content, wrap="word", width=30, height=4,
                                            font=("Segoe UI", 9), bg=DEFAULT_BG_COLOR, fg=TEXT_COLOR,
                                            insertbackground=TEXT_COLOR, relief="sunken", bd=2)
        info_text.pack(fill="x", pady=(0, 10))

        # Descrizione
        tk.Label(content, text="Descrizione Colonia:",
                font=("Segoe UI", 12),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", pady=(0, 5))

        description_text = scrolledtext.ScrolledText(content, wrap="word", width=30, height=4,
                                                    font=("Segoe UI", 10),
                                                    bg=DEFAULT_BG_COLOR, fg=TEXT_COLOR,
                                                    insertbackground=TEXT_COLOR)
        description_text.pack(fill="x", pady=(0, 15))


        def on_species_select(event):
            species = species_combo.get()
            if species in self.species_db:
                data = self.species_db[species]
                
                description_text.delete("1.0", tk.END)
                description_text.insert("1.0", data["description"])
                
                info_text.delete("1.0", tk.END)
                info_text.insert("1.0", data["notes"])

        species_combo.bind("<<ComboboxSelected>>", on_species_select)
        

        tk.Label(content, text="Data di raccolta:",
                font=("Segoe UI", 12),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", pady=(0, 5))

        date_entry = DateEntry(content, font=("Segoe UI", 12), date_pattern='yyyy-mm-dd')
        date_entry.pack(fill="x", pady=(0, 10))
        
        tk.Label(content, text="Popolazione iniziale:",
                font=("Segoe UI", 12),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", pady=(0, 5))
        
        pop_var = tk.StringVar(value="0")
        pop_entry = tk.Entry(content, textvariable=pop_var,
                             font=("Segoe UI", 12),
                             width=10)
        pop_entry.pack(anchor="w", pady=(0, 20))

        btn_frame = tk.Frame(content, bg=CARD_BG_COLOR)
        btn_frame.pack(fill="x")

        def save_colony():
            name = name_var.get().strip()
            description = description_text.get("1.0", tk.END).strip()
            
            if not name:
                messagebox.showerror("Errore", "Il nome della colonia è obbligatorio!", parent=dialog)
                return
                
            if len(name) > 50:
                 messagebox.showerror("Errore", "Il nome è troppo lungo (max 50 caratteri).", parent=dialog)
                 return

            date_str = date_entry.get()
            try:
                datetime.strptime(date_str, '%Y-%m-%d')
            except ValueError:
                messagebox.showerror("Errore", "Formato data non valido. Usa YYYY-MM-DD.", parent=dialog)
                return
            
            try:
                initial_pop = int(pop_var.get())
                if initial_pop < 0: raise ValueError
            except ValueError:
                messagebox.showerror("Errore", "La popolazione deve essere un numero intero positivo.", parent=dialog)
                return

            new_colony = {
                "name": name,
                "species": species_var.get(), # Save species
                "collection_date": date_entry.get(),
                "description": description,
                "notes": info_text.get("1.0", tk.END).strip(), # Save updated info as notes
                "images": [],
                "profile_image": "",
                "feeding_schedule": [],
                "recurring_schedule": [],
                "feeding_history": [],
                "history": [{
                    "timestamp": datetime.now().isoformat(),
                    "population": initial_pop,
                    "mortalita": 0,
                    "presenza_uova_larve": "non registrato",
                    "stato_salute_generale": "non registrato"
                }],
                "created_at": datetime.now().strftime('%Y-%m-%d %H:%M')
            }

            self.colonies.append(new_colony)
            self.save_data()
            dialog.destroy()
            
            # Se è la prima colonia, ricrea l'interfaccia principale
            if len(self.colonies) == 1:
                self.create_main_frame()
            else:
                self.display_colonies()
                
            messagebox.showinfo("Successo", f"Colonia '{name}' creata con successo!")

        ttk.Button(btn_frame, text="Salva",
                  style="Success.TButton",
                  command=save_colony).pack(side="right", padx=5)

        ttk.Button(btn_frame, text="Annulla",
                  style="Modern.TButton",
                  command=dialog.destroy).pack(side="right", padx=5)

        dialog.bind('<Return>', lambda e: save_colony())

    def show_colony(self, colony):
        self.current_colony = colony
        self.clear_frame()
        self.update_colony_view()
        
    def update_colony_view(self):
        self.clear_frame()

        main_container = tk.Frame(self.root, bg=DEFAULT_BG_COLOR)
        main_container.pack(fill="both", expand=True)

        self._create_colony_header(main_container)

        content = tk.Frame(main_container, bg=DEFAULT_BG_COLOR)
        content.pack(fill="both", expand=True, padx=20, pady=20)

        paned_window = tk.PanedWindow(content, orient=tk.HORIZONTAL, 
                                     sashrelief=tk.RAISED, sashwidth=5,
                                     bg=DEFAULT_BG_COLOR)
        paned_window.pack(fill="both", expand=True)
        
        left_panel = self._create_left_panel(paned_window)
        right_panel = self._create_right_panel(paned_window)
        
        paned_window.add(left_panel)
        paned_window.add(right_panel)
        paned_window.sash_place(0, 350, 0)

        self.update_background_image()

    def _create_colony_header(self, parent_frame):
        header = tk.Frame(parent_frame, bg=CARD_BG_COLOR, height=80)
        header.pack(fill="x")
        header.pack_propagate(False)

        header_content = tk.Frame(header, bg=CARD_BG_COLOR)
        header_content.pack(fill="both", expand=True, padx=20, pady=15)

        ttk.Button(header_content, text="← Indietro",
                  style="Modern.TButton",
                  command=self.create_main_frame).pack(side="left")

        tk.Label(header_content,
                text=f"🐜 {self.current_colony['name']}",
                font=("Segoe UI", 18, "bold"),
                fg=TEXT_COLOR,
                bg=CARD_BG_COLOR).pack(side="left", padx=20)

        # Pulsante per modificare la colonia
        ttk.Button(header_content, text="✏️ Modifica",
                  style="Modern.TButton",
                  command=self.edit_colony).pack(side="left", padx=10)

        # Pulsante per esportare i dati
        ttk.Button(header_content, text="📤 Esporta",
                  style="Success.TButton",
                  command=self.export_colony).pack(side="right", padx=10)

    def edit_colony(self):
        dialog = tk.Toplevel(self.root)
        dialog.title("Modifica Colonia")
        dialog.geometry("500x700")
        dialog.configure(bg=CARD_BG_COLOR)
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.focus_set()

        dialog.geometry(f"+{self.root.winfo_rootx()+150}+{self.root.winfo_rooty()+50}")

        content = tk.Frame(dialog, bg=CARD_BG_COLOR)
        content.pack(fill="both", expand=True, padx=30, pady=30)

        tk.Label(content, text="Modifica Colonia",
                font=("Segoe UI", 16, "bold"),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(pady=(0, 20))

        tk.Label(content, text="Nome della colonia:",
                font=("Segoe UI", 12),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", pady=(0, 5))

        name_var = tk.StringVar(value=self.current_colony["name"])
        name_entry = tk.Entry(content, textvariable=name_var,
                             font=("Segoe UI", 12),
                             width=30)
        name_entry.pack(fill="x", pady=(0, 5))
        name_entry.focus()
        
        # --- Sezione Specie ---
        tk.Label(content, text="Specie (Database):", font=("Segoe UI", 10), fg="#bdc3c7", bg=CARD_BG_COLOR).pack(anchor="w", pady=(10, 0))
        
        species_frame = tk.Frame(content, bg=CARD_BG_COLOR)
        species_frame.pack(fill="x", pady=(0, 5))
        
        species_var = tk.StringVar(value=self.current_colony.get("species", ""))
        all_species = sorted(list(self.species_db.keys()))
        species_combo = ttk.Combobox(species_frame, textvariable=species_var, values=all_species)
        species_combo.pack(side="left", fill="x", expand=True)
        
        def save_new_species():
            name = species_var.get().strip()
            notes = info_text.get("1.0", tk.END).strip()
            desc = description_text.get("1.0", tk.END).strip()
            
            if not name:
                messagebox.showerror("Errore", "Inserisci il nome della specie.")
                return
            if name in self.species_db and name not in self.custom_species:
                messagebox.showerror("Errore", "Non puoi sovrascrivere le specie predefinite.")
                return
            
            # Salva
            self.custom_species[name] = {"description": desc, "notes": notes}
            self.species_db[name] = self.custom_species[name]
            self.save_data()
            
            # Aggiorna combo
            species_combo['values'] = sorted(list(self.species_db.keys()))
            messagebox.showinfo("Successo", f"Specie '{name}' salvata nel database!")

        ttk.Button(species_frame, text="💾 Salva Specie", command=save_new_species, style="Modern.TButton").pack(side="left", padx=(5, 0))
        
        # Info Box Modificabile
        tk.Label(content, text="Info Cura / Note (Modificabile):", font=("Segoe UI", 10, "bold"), fg="#bdc3c7", bg=CARD_BG_COLOR).pack(anchor="w")
        info_text = scrolledtext.ScrolledText(content, wrap="word", width=30, height=4,
                                            font=("Segoe UI", 9), bg=DEFAULT_BG_COLOR, fg=TEXT_COLOR,
                                            insertbackground=TEXT_COLOR, relief="sunken", bd=2)
        info_text.insert("1.0", self.current_colony.get("notes", ""))
        info_text.pack(fill="x", pady=(0, 10))


        tk.Label(content, text="Descrizione:",
                font=("Segoe UI", 12),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", pady=(0, 5))

        description_text = scrolledtext.ScrolledText(content, wrap="word", width=30, height=4,
                                                    font=("Segoe UI", 10),
                                                    bg=DEFAULT_BG_COLOR, fg=TEXT_COLOR,
                                                    insertbackground=TEXT_COLOR)
        description_text.insert(tk.END, self.current_colony.get("description", ""))
        description_text.pack(fill="x", pady=(0, 15))


        def on_species_select(event):
            species = species_combo.get()
            if species in self.species_db:
                data = self.species_db[species]
                
                description_text.delete("1.0", tk.END)
                description_text.insert("1.0", data["description"])
                
                info_text.delete("1.0", tk.END)
                info_text.insert("1.0", data["notes"])

        species_combo.bind("<<ComboboxSelected>>", on_species_select)


        tk.Label(content, text="Data di raccolta:",
                font=("Segoe UI", 12),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", pady=(0, 5))

        date_entry = DateEntry(content, font=("Segoe UI", 12), date_pattern='yyyy-mm-dd')
        date_entry.set_date(self.current_colony["collection_date"])
        date_entry.pack(fill="x", pady=(0, 20))

        btn_frame = tk.Frame(content, bg=CARD_BG_COLOR)
        btn_frame.pack(fill="x")

        def save_changes():
            name = name_var.get().strip()
            description = description_text.get("1.0", tk.END).strip()
            if not name:
                messagebox.showerror("Errore", "Il nome della colonia è obbligatorio!")
                return
            
            # Update data
            self.current_colony["name"] = name
            self.current_colony["description"] = description
            self.current_colony["collection_date"] = date_entry.get()
            self.current_colony["species"] = species_var.get()
            self.current_colony["notes"] = info_text.get("1.0", tk.END).strip()
            
            self.save_data()
            dialog.destroy()
            self.update_colony_view()
            messagebox.showinfo("Successo", "Modifiche salvate con successo!")

        ttk.Button(btn_frame, text="Salva Modifiche",
                  style="Success.TButton",
                  command=save_changes).pack(side="right", padx=5)

        ttk.Button(btn_frame, text="Annulla",
                  style="Modern.TButton",
                  command=dialog.destroy).pack(side="right", padx=5)

        dialog.bind('<Return>', lambda e: save_changes())

    def export_colony(self):
        file_path = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("JSON files", "*.json")],
            title="Esporta dati colonia"
        )
        
        if not file_path:
            return
            
        try:
            with open(file_path, 'w', encoding='utf-8') as f:
                json.dump(self.current_colony, f, indent=2, ensure_ascii=False)
            messagebox.showinfo("Successo", "Dati della colonia esportati con successo!")
        except Exception as e:
            messagebox.showerror("Errore", f"Errore durante l'esportazione: {str(e)}")
    
    def import_colony(self):
        """Importa una colonia da un file JSON."""
        file_path = filedialog.askopenfilename(
            filetypes=[("JSON files", "*.json")],
            title="Importa colonia da file"
        )
        
        if not file_path:
            return
            
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                colony_data = json.load(f)
            
            # Validazione base
            if not isinstance(colony_data, dict) or 'name' not in colony_data:
                messagebox.showerror("Errore", "Il file non contiene dati di colonia validi.")
                return
            
            # Controlla se esiste già una colonia con lo stesso nome
            existing_names = [c['name'].lower() for c in self.colonies]
            original_name = colony_data['name']
            if original_name.lower() in existing_names:
                # Aggiungi suffisso per evitare conflitti
                counter = 1
                while f"{original_name} ({counter})".lower() in existing_names:
                    counter += 1
                colony_data['name'] = f"{original_name} ({counter})"
                messagebox.showinfo("Info", f"Colonia rinominata in '{colony_data['name']}' per evitare conflitti.")
            
            # Inizializza campi mancanti
            colony_data.setdefault('history', [])
            colony_data.setdefault('feeding_schedule', [])
            colony_data.setdefault('recurring_schedule', [])
            colony_data.setdefault('feeding_history', [])
            colony_data.setdefault('notes', '')
            colony_data.setdefault('images', [])
            colony_data.setdefault('profile_image', '')
            
            self.colonies.append(colony_data)
            self.save_data()
            self.create_main_frame()
            messagebox.showinfo("Successo", f"Colonia '{colony_data['name']}' importata con successo!")
        except json.JSONDecodeError:
            messagebox.showerror("Errore", "Il file non è un JSON valido.")
        except Exception as e:
            messagebox.showerror("Errore", f"Errore durante l'esportazione: {str(e)}")

    def _create_left_panel(self, parent):
        left_panel = tk.Frame(parent, bg=CARD_BG_COLOR, width=350)
        left_panel.pack_propagate(False)

        notebook = ttk.Notebook(left_panel)
        notebook.pack(fill="both", expand=True, padx=10, pady=10)
        
        info_tab = tk.Frame(notebook, bg=CARD_BG_COLOR)
        self._create_info_tab(info_tab)
        notebook.add(info_tab, text="ℹ️ Info")
        
        feeding_tab = tk.Frame(notebook, bg=CARD_BG_COLOR)
        self._create_feeding_tab(feeding_tab)
        notebook.add(feeding_tab, text="🍯 Alimentazione")

        monitoring_tab = tk.Frame(notebook, bg=CARD_BG_COLOR)
        self._create_monitoring_tab(monitoring_tab)
        notebook.add(monitoring_tab, text="📊 Monitoraggio")
        
        return left_panel

    def _create_info_tab(self, parent):
        content = tk.Frame(parent, bg=CARD_BG_COLOR)
        content.pack(fill="both", expand=True, padx=10, pady=10)
        
        tk.Label(content, text="Informazioni Colonia",
                font=("Segoe UI", 14, "bold"),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", pady=(0, 15))

        tk.Label(content, text=f"📅 Data raccolta: {self.current_colony['collection_date']}",
                font=("Segoe UI", 11),
                fg="#bdc3c7", bg=CARD_BG_COLOR).pack(anchor="w", pady=5)
        
        if self.current_colony.get("species"):
             tk.Label(content, text=f"🐜 Specie: {self.current_colony['species']}",
                font=("Segoe UI", 11),
                fg=ACCENT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", pady=5)
        
        # Display dei dati storici più recenti
        last_history = self.current_colony['history'][-1] if self.current_colony['history'] else None
        
        if last_history:
            tk.Label(content, text="Ultimo aggiornamento:",
                    font=("Segoe UI", 11, "italic"),
                    fg="#95a5a6", bg=CARD_BG_COLOR).pack(anchor="w", pady=(10, 5))
            
            tk.Label(content, text=f"👥 Popolazione: {last_history['population']}",
                    font=("Segoe UI", 11), fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w")
            tk.Label(content, text=f"💀 Mortalità: {last_history['mortalita']}",
                    font=("Segoe UI", 11), fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w")
            tk.Label(content, text=f"🥚 Uova/Larve: {last_history['presenza_uova_larve']}",
                    font=("Segoe UI", 11), fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w")
            tk.Label(content, text=f"❤️ Salute: {last_history['stato_salute_generale']}",
                    font=("Segoe UI", 11), fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w")


        desc_section = tk.Frame(content, bg=CARD_BG_COLOR)
        desc_section.pack(fill="x", pady=(10, 10))

        tk.Label(desc_section, text="Descrizione Colonia",
                font=("Segoe UI", 14, "bold"),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", pady=(0, 10))

        self.description_text_area = scrolledtext.ScrolledText(desc_section, wrap="word", height=5,
                                                              font=("Segoe UI", 10),
                                                              bg=DEFAULT_BG_COLOR, fg=TEXT_COLOR,
                                                              insertbackground=TEXT_COLOR)
        self.description_text_area.insert(tk.END, self.current_colony.get("description", ""))
        self.description_text_area.pack(fill="x", pady=(0, 5))

        ttk.Button(desc_section, text="Salva Descrizione",
                  style="Success.TButton",
                  command=self.save_description).pack(pady=5)

        img_section = tk.Frame(content, bg=CARD_BG_COLOR)
        img_section.pack(fill="x", pady=(10, 0))

        tk.Label(img_section, text="Immagine Profilo",
                font=("Segoe UI", 14, "bold"),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", pady=(0, 10))

        self.profile_img_label = tk.Label(img_section, bg=DEFAULT_BG_COLOR)
        self.profile_img_label.pack(pady=10)
        self.update_profile_image()

        ttk.Button(img_section, text="📷 Cambia Immagine",
                  style="Modern.TButton",
                  command=self.change_profile_image).pack(pady=5)

    def _create_feeding_tab(self, parent):
        content = tk.Frame(parent, bg=CARD_BG_COLOR)
        content.pack(fill="both", expand=True, padx=10, pady=10)

        feeding_notebook = ttk.Notebook(content)
        feeding_notebook.pack(fill="both", expand=True)

        # Tab Promemoria Singoli
        single_tab = tk.Frame(feeding_notebook, bg=CARD_BG_COLOR)
        self._create_single_feeding_tab(single_tab)
        feeding_notebook.add(single_tab, text="Promemoria")

        # Tab Promemoria Ricorrenti
        recurring_tab = tk.Frame(feeding_notebook, bg=CARD_BG_COLOR)
        self._create_recurring_feeding_tab(recurring_tab)
        feeding_notebook.add(recurring_tab, text="Ricorrenti")

        # Tab Cronologia
        history_tab = tk.Frame(feeding_notebook, bg=CARD_BG_COLOR)
        self._create_feeding_history_tab(history_tab)
        feeding_notebook.add(history_tab, text="Cronologia")

    def _create_single_feeding_tab(self, parent):
        # Frame per l'inserimento
        add_frame = tk.Frame(parent, bg=CARD_BG_COLOR, relief="groove", bd=1)
        add_frame.pack(fill="x", padx=5, pady=5)

        tk.Label(add_frame, text="Aggiungi Promemoria Singolo", font=("Segoe UI", 12, "bold"),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", padx=10, pady=5)
        
        input_frame = tk.Frame(add_frame, bg=CARD_BG_COLOR)
        input_frame.pack(fill="x", padx=10, pady=5)

        # Data e ora
        date_frame = tk.Frame(input_frame, bg=CARD_BG_COLOR)
        date_frame.pack(fill="x", pady=2)
        tk.Label(date_frame, text="Data:", font=("Segoe UI", 10), fg="#bdc3c7", bg=CARD_BG_COLOR).pack(side="left")
        self.feed_date_entry = DateEntry(date_frame, font=("Segoe UI", 10), date_pattern='yyyy-mm-dd')
        self.feed_date_entry.pack(side="left", padx=(10, 0))

        time_frame = tk.Frame(input_frame, bg=CARD_BG_COLOR)
        time_frame.pack(fill="x", pady=2)
        tk.Label(time_frame, text="Orario:", font=("Segoe UI", 10), fg="#bdc3c7", bg=CARD_BG_COLOR).pack(side="left")
        self.hour_var = tk.StringVar(value=datetime.now().strftime("%H"))
        self.hour_spin = tk.Spinbox(time_frame, from_=0, to=23, width=3, textvariable=self.hour_var, font=("Segoe UI", 10))
        self.hour_spin.pack(side="left", padx=(10, 5))
        tk.Label(time_frame, text=":", font=("Segoe UI", 12, "bold"), fg="#bdc3c7", bg=CARD_BG_COLOR).pack(side="left")
        self.minute_var = tk.StringVar(value=datetime.now().strftime("%M"))
        self.minute_spin = tk.Spinbox(time_frame, from_=0, to=59, width=3, textvariable=self.minute_var, font=("Segoe UI", 10))
        self.minute_spin.pack(side="left", padx=(5, 10))

        # Tipo di cibo
        food_type_frame = tk.Frame(input_frame, bg=CARD_BG_COLOR)
        food_type_frame.pack(fill="x", pady=2)
        tk.Label(food_type_frame, text="Tipo Cibo:", font=("Segoe UI", 10), fg="#bdc3c7", bg=CARD_BG_COLOR).pack(side="left")
        self.food_type_var = ttk.Combobox(food_type_frame, values=["Proteine", "Zucchero", "Insetto", "Miele", "Acqua", "Altro"], state="readonly")
        self.food_type_var.set("Proteine")
        self.food_type_var.pack(side="left", padx=10)

        # Quantità
        quantity_frame = tk.Frame(input_frame, bg=CARD_BG_COLOR)
        quantity_frame.pack(fill="x", pady=2)
        tk.Label(quantity_frame, text="Quantità:", font=("Segoe UI", 10), fg="#bdc3c7", bg=CARD_BG_COLOR).pack(side="left")
        self.quantity_entry = tk.Entry(quantity_frame, width=15)
        self.quantity_entry.pack(side="left", padx=10)

        # Descrizione
        tk.Label(add_frame, text="Descrizione (opzionale):", font=("Segoe UI", 10), fg="#bdc3c7", bg=CARD_BG_COLOR).pack(anchor="w", padx=10, pady=(5, 0))
        self.feed_description_text = scrolledtext.ScrolledText(add_frame, wrap="word", width=30, height=3, font=("Segoe UI", 10), bg=DEFAULT_BG_COLOR, fg=TEXT_COLOR, insertbackground=TEXT_COLOR)
        self.feed_description_text.pack(fill="x", padx=10, pady=5)

        ttk.Button(add_frame, text="🕐 Aggiungi Promemoria", style="Success.TButton",
                  command=lambda: self.add_feeding_schedule(
                      self.feed_date_entry.get(), f"{self.hour_var.get().zfill(2)}:{self.minute_var.get().zfill(2)}",
                      self.feed_description_text.get("1.0", tk.END).strip(),
                      self.food_type_var.get(), self.quantity_entry.get()
                  )).pack(pady=10)

        # Frame per la lista dei promemoria
        tk.Label(parent, text="Promemoria Attivi", font=("Segoe UI", 12, "bold"),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", padx=5, pady=(10, 5))
        
        self.single_list_frame = tk.Frame(parent, bg=CARD_BG_COLOR)
        self.single_list_frame.pack(fill="both", expand=True, padx=5, pady=5)
        self.update_single_feeding_list(self.single_list_frame)
    
    def _create_recurring_feeding_tab(self, parent):
        # Frame per l'inserimento
        add_frame = tk.Frame(parent, bg=CARD_BG_COLOR, relief="groove", bd=1)
        add_frame.pack(fill="x", padx=5, pady=5)

        tk.Label(add_frame, text="Aggiungi Promemoria Ricorrente", font=("Segoe UI", 12, "bold"),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", padx=10, pady=5)
        
        input_frame = tk.Frame(add_frame, bg=CARD_BG_COLOR)
        input_frame.pack(fill="x", padx=10, pady=5)

        # Data di inizio e intervallo
        start_date_frame = tk.Frame(input_frame, bg=CARD_BG_COLOR)
        start_date_frame.pack(fill="x", pady=2)
        tk.Label(start_date_frame, text="Data di inizio:", font=("Segoe UI", 10), fg="#bdc3c7", bg=CARD_BG_COLOR).pack(side="left")
        self.recurring_start_date_entry = DateEntry(start_date_frame, font=("Segoe UI", 10), date_pattern='yyyy-mm-dd')
        self.recurring_start_date_entry.pack(side="left", padx=(10, 0))

        interval_frame = tk.Frame(input_frame, bg=CARD_BG_COLOR)
        interval_frame.pack(fill="x", pady=2)
        tk.Label(interval_frame, text="Ripeti ogni (giorni):", font=("Segoe UI", 10), fg="#bdc3c7", bg=CARD_BG_COLOR).pack(side="left")
        self.recurring_interval_var = tk.StringVar(value="3")
        self.recurring_interval_spin = tk.Spinbox(interval_frame, from_=1, to=30, width=5, textvariable=self.recurring_interval_var, font=("Segoe UI", 10))
        self.recurring_interval_spin.pack(side="left", padx=(10, 0))

        # Tipo di cibo
        food_type_frame = tk.Frame(input_frame, bg=CARD_BG_COLOR)
        food_type_frame.pack(fill="x", pady=2)
        tk.Label(food_type_frame, text="Tipo Cibo:", font=("Segoe UI", 10), fg="#bdc3c7", bg=CARD_BG_COLOR).pack(side="left")
        self.recurring_food_type_var = ttk.Combobox(food_type_frame, values=["Proteine", "Zucchero", "Insetto", "Miele", "Acqua", "Altro"], state="readonly")
        self.recurring_food_type_var.set("Proteine")
        self.recurring_food_type_var.pack(side="left", padx=10)

        # Quantità
        quantity_frame = tk.Frame(input_frame, bg=CARD_BG_COLOR)
        quantity_frame.pack(fill="x", pady=2)
        tk.Label(quantity_frame, text="Quantità:", font=("Segoe UI", 10), fg="#bdc3c7", bg=CARD_BG_COLOR).pack(side="left")
        self.recurring_quantity_entry = tk.Entry(quantity_frame, width=15)
        self.recurring_quantity_entry.pack(side="left", padx=10)
        
        ttk.Button(add_frame, text="🔄 Aggiungi Ricorrenza", style="Success.TButton",
                  command=self.add_recurring_schedule).pack(pady=10)

        # Frame per la lista dei promemoria ricorrenti
        tk.Label(parent, text="Promemoria Ricorrenti", font=("Segoe UI", 12, "bold"),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", padx=5, pady=(10, 5))
        
        self.recurring_list_frame = tk.Frame(parent, bg=CARD_BG_COLOR)
        self.recurring_list_frame.pack(fill="both", expand=True, padx=5, pady=5)
        self.update_recurring_feeding_list()

    def _create_feeding_history_tab(self, parent):
        tk.Label(parent, text="Cronologia Alimentazione", font=("Segoe UI", 14, "bold"),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", padx=10, pady=10)

        self.feeding_history_frame = tk.Frame(parent, bg=CARD_BG_COLOR)
        self.feeding_history_frame.pack(fill="both", expand=True, padx=10, pady=10)
        self.update_feeding_history_list()
    
    def add_feeding_schedule(self, date_str, time_str, description, food_type, quantity):
        if not date_str:
            messagebox.showerror("Errore", "Seleziona una data per il promemoria.")
            return

        try:
            datetime_obj = datetime.strptime(f"{date_str} {time_str}", "%Y-%m-%d %H:%M")
            new_schedule = {
                "datetime": datetime_obj.isoformat(),
                "description": description,
                "food_type": food_type,
                "quantity": quantity
            }
            self.current_colony["feeding_schedule"].append(new_schedule)
            self.save_data()
            self.update_single_feeding_list()
            messagebox.showinfo("Successo", "Promemoria singolo aggiunto con successo!")
        except ValueError:
            messagebox.showerror("Errore", "Formato data/ora non valido.")

    def add_recurring_schedule(self):
        start_date_str = self.recurring_start_date_entry.get()
        interval_str = self.recurring_interval_var.get()
        food_type = self.recurring_food_type_var.get()
        quantity = self.recurring_quantity_entry.get()

        if not start_date_str or not interval_str:
            messagebox.showerror("Errore", "Data di inizio e intervallo sono obbligatori.")
            return
        
        try:
            start_date = datetime.strptime(start_date_str, '%Y-%m-%d').date()
            interval = int(interval_str)
        except ValueError:
            messagebox.showerror("Errore", "Formato data/intervallo non valido.")
            return

        new_recurring = {
            "start_date": start_date.isoformat(),
            "interval": interval,
            "food_type": food_type,
            "quantity": quantity
        }
        self.current_colony["recurring_schedule"].append(new_recurring)
        self.save_data()
        self.update_recurring_feeding_list()
        messagebox.showinfo("Successo", "Promemoria ricorrente aggiunto con successo!")

    def remove_feeding_schedule(self, schedule_to_remove, is_recurring=False):
        if is_recurring:
            schedule_list = self.current_colony["recurring_schedule"]
            update_func = self.update_recurring_feeding_list
            message_type = "ricorrente"
        else:
            schedule_list = self.current_colony["feeding_schedule"]
            update_func = self.update_single_feeding_list
            message_type = "singolo"

        if schedule_to_remove in schedule_list:
            if messagebox.askyesno("Elimina Promemoria", f"Sei sicuro di voler eliminare questo promemoria {message_type}?"):
                schedule_list.remove(schedule_to_remove)
                self.save_data()
                update_func()
                messagebox.showinfo("Successo", "Promemoria eliminato!")
    
    def complete_feeding_reminder(self, reminder):
        # Aggiungi il pasto alla cronologia
        new_history_entry = {
            "datetime": datetime.now().isoformat(),
            "food_type": reminder['food_type'],
            "quantity": reminder['quantity'],
            "description": reminder['description']
        }
        self.current_colony['feeding_history'].append(new_history_entry)
        
        # Rimuovi il promemoria dalla lista
        self.current_colony['feeding_schedule'].remove(reminder)
        
        self.save_data()
        self.update_colony_view() # Aggiorna tutte le schede
        messagebox.showinfo("Successo", f"Pasto registrato nella cronologia!")

    def update_single_feeding_list(self, parent_frame=None):
        if parent_frame is None: parent_frame = self.single_list_frame

        for widget in parent_frame.winfo_children():
            widget.destroy()

        feeding_schedule = sorted(self.current_colony.get("feeding_schedule", []), key=lambda x: x['datetime'])
        
        if not feeding_schedule:
            tk.Label(parent_frame, text="Nessun promemoria di alimentazione",
                    font=("Segoe UI", 10, "italic"),
                    fg="#95a5a6", bg=CARD_BG_COLOR).pack(pady=10)
            return

        for schedule in feeding_schedule:
            try:
                schedule_dt = datetime.fromisoformat(schedule['datetime'])
                description = schedule.get('description', '')
                food_type = schedule.get('food_type', '')
                quantity = schedule.get('quantity', '')
                
                text = f"📅 {schedule_dt.strftime('%d-%m-%Y')} alle {schedule_dt.strftime('%H:%M')}"
                if food_type or quantity:
                    text += f"\n🍯 Cibo: {food_type} ({quantity})"
                if description:
                    text += f"\n📝 Note: {description}"
                
                item_frame = tk.Frame(parent_frame, bg=CARD_BG_COLOR)
                item_frame.pack(fill="x", pady=2)
                
                tk.Label(item_frame, text=text,
                        font=("Segoe UI", 10),
                        fg=TEXT_COLOR, bg=CARD_BG_COLOR, justify="left").pack(side="left", padx=5)

                if schedule_dt < datetime.now():
                    ttk.Button(item_frame, text="✅ Nutrito", style="Success.TButton",
                               command=lambda s=schedule: self.complete_feeding_reminder(s)).pack(side="right", padx=5)
                
                ttk.Button(item_frame, text="🗑️", style="Danger.TButton",
                          command=lambda s=schedule: self.remove_feeding_schedule(s)).pack(side="right", padx=5)

            except (ValueError, KeyError):
                pass
    
    def update_recurring_feeding_list(self):
        for widget in self.recurring_list_frame.winfo_children():
            widget.destroy()
        
        recurring_schedule = self.current_colony.get("recurring_schedule", [])
        if not recurring_schedule:
            tk.Label(self.recurring_list_frame, text="Nessun promemoria ricorrente",
                    font=("Segoe UI", 10, "italic"),
                    fg="#95a5a6", bg=CARD_BG_COLOR).pack(pady=10)
            return

        for recurring in recurring_schedule:
            start_date_str = recurring.get('start_date', 'N/D')
            interval = recurring.get('interval', 'N/D')
            food_type = recurring.get('food_type', '')
            quantity = recurring.get('quantity', '')

            text = f"▶️ Inizia il: {start_date_str}\n"
            text += f"🔄 Ripeti ogni: {interval} giorni\n"
            text += f"🍯 Cibo: {food_type} ({quantity})"

            item_frame = tk.Frame(self.recurring_list_frame, bg=CARD_BG_COLOR)
            item_frame.pack(fill="x", pady=2)

            tk.Label(item_frame, text=text,
                    font=("Segoe UI", 10),
                    fg=TEXT_COLOR, bg=CARD_BG_COLOR, justify="left").pack(side="left", padx=5)
            
            ttk.Button(item_frame, text="🗑️", style="Danger.TButton",
                      command=lambda r=recurring: self.remove_feeding_schedule(r, is_recurring=True)).pack(side="right", padx=5)

    def update_feeding_history_list(self):
        for widget in self.feeding_history_frame.winfo_children():
            widget.destroy()

        feeding_history = sorted(self.current_colony.get("feeding_history", []), key=lambda x: x['datetime'], reverse=True)

        if not feeding_history:
            tk.Label(self.feeding_history_frame, text="Nessun pasto registrato nella cronologia.",
                    font=("Segoe UI", 10, "italic"),
                    fg="#95a5a6", bg=CARD_BG_COLOR).pack(pady=10)
            return

        for record in feeding_history:
            try:
                record_dt = datetime.fromisoformat(record['datetime'])
                food_type = record.get('food_type', 'N/D')
                quantity = record.get('quantity', 'N/D')
                description = record.get('description', 'Nessuna descrizione')

                text = f"📅 {record_dt.strftime('%d-%m-%Y %H:%M')}\n"
                text += f"🍯 Cibo: {food_type} ({quantity})\n"
                text += f"📝 Note: {description}"
                
                item_frame = tk.Frame(self.feeding_history_frame, bg=DEFAULT_BG_COLOR)
                item_frame.pack(fill="x", pady=2)
                
                tk.Label(item_frame, text=text,
                        font=("Segoe UI", 10),
                        fg=TEXT_COLOR, bg=DEFAULT_BG_COLOR, justify="left").pack(side="left", padx=5)

            except (ValueError, KeyError):
                pass

    def _create_monitoring_tab(self, parent):
        content = tk.Frame(parent, bg=CARD_BG_COLOR)
        content.pack(fill="both", expand=True, padx=10, pady=10)

        # Frame per il grafico
        graph_frame = tk.Frame(content, bg=DEFAULT_BG_COLOR)
        graph_frame.pack(fill="both", expand=True)

        self.graph_canvas = tk.Canvas(graph_frame, bg=DEFAULT_BG_COLOR, highlightthickness=0)
        self.graph_canvas.pack(fill="both", expand=True, padx=5, pady=5)
        self.graph_canvas.bind("<Configure>", self.draw_population_graph)

        # Frame per l'inserimento dei dati
        entry_frame = tk.Frame(content, bg=CARD_BG_COLOR, relief="raised", bd=1)
        entry_frame.pack(fill="x", padx=10, pady=10)
        
        tk.Label(entry_frame, text="Registra Nuovi Dati", font=("Segoe UI", 12, "bold"),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", padx=10, pady=5)

        # Popolazione
        pop_frame = tk.Frame(entry_frame, bg=CARD_BG_COLOR)
        pop_frame.pack(fill="x", padx=10, pady=2)
        tk.Label(pop_frame, text="Popolazione:", fg="#bdc3c7", bg=CARD_BG_COLOR).pack(side="left")
        self.pop_entry = tk.Entry(pop_frame, width=10)
        self.pop_entry.pack(side="left", padx=5)

        # Mortalità
        mortality_frame = tk.Frame(entry_frame, bg=CARD_BG_COLOR)
        mortality_frame.pack(fill="x", padx=10, pady=2)
        tk.Label(mortality_frame, text="Mortalità:", fg="#bdc3c7", bg=CARD_BG_COLOR).pack(side="left")
        self.mortality_entry = tk.Entry(mortality_frame, width=10)
        self.mortality_entry.pack(side="left", padx=5)
        
        # Uova/Larve
        eggs_frame = tk.Frame(entry_frame, bg=CARD_BG_COLOR)
        eggs_frame.pack(fill="x", padx=10, pady=2)
        tk.Label(eggs_frame, text="Uova/Larve:", fg="#bdc3c7", bg=CARD_BG_COLOR).pack(side="left")
        self.eggs_var = ttk.Combobox(eggs_frame, values=["non registrato", "nessuna", "poche", "abbondanti"], state="readonly")
        self.eggs_var.set("non registrato")
        self.eggs_var.pack(side="left", padx=5)
        
        # Stato salute
        health_frame = tk.Frame(entry_frame, bg=CARD_BG_COLOR)
        health_frame.pack(fill="x", padx=10, pady=2)
        tk.Label(health_frame, text="Salute:", fg="#bdc3c7", bg=CARD_BG_COLOR).pack(side="left")
        self.health_var = ttk.Combobox(health_frame, values=["non registrato", "eccellente", "buona", "media", "scarsa"], state="readonly")
        self.health_var.set("non registrato")
        self.health_var.pack(side="left", padx=5)
        
        ttk.Button(entry_frame, text="Salva Dati", style="Success.TButton",
                  command=self.save_monitoring_data).pack(pady=10)
        
    def save_monitoring_data(self):
        try:
            population = int(self.pop_entry.get())
            mortality = int(self.mortality_entry.get())
        except ValueError:
            messagebox.showerror("Errore", "Popolazione e mortalità devono essere numeri interi.")
            return

        new_record = {
            "timestamp": datetime.now().isoformat(),
            "population": population,
            "mortalita": mortality,
            "presenza_uova_larve": self.eggs_var.get(),
            "stato_salute_generale": self.health_var.get()
        }
        
        self.current_colony["history"].append(new_record)
        self.save_data()
        
        # Pulisci i campi e aggiorna la vista
        self.pop_entry.delete(0, tk.END)
        self.mortality_entry.delete(0, tk.END)
        self.eggs_var.set("non registrato")
        self.health_var.set("non registrato")

        # Aggiorna la vista per mostrare i nuovi dati
        self.update_colony_view()
        
        messagebox.showinfo("Successo", "Dati di monitoraggio salvati con successo!")

    def draw_population_graph(self, event=None):
        if not self.current_colony or not hasattr(self, 'graph_canvas'):
            return
            
        self.graph_canvas.delete("all")
        
        if not self.current_colony.get("history"):
            self.graph_canvas.create_text(self.graph_canvas.winfo_width()/2,
                                          self.graph_canvas.winfo_height()/2,
                                          text="Nessun dato storico per il grafico.",
                                          fill="#95a5a6", font=("Segoe UI", 12))
            return

        # Dati da plottare
        history_data = sorted(self.current_colony["history"], key=lambda x: x['timestamp'])
        
        if len(history_data) < 2:
            self.graph_canvas.create_text(self.graph_canvas.winfo_width()/2,
                                          self.graph_canvas.winfo_height()/2,
                                          text="Aggiungi almeno due dati per visualizzare il grafico.",
                                          fill="#95a5a6", font=("Segoe UI", 12))
            return
            
        timestamps = [datetime.fromisoformat(d['timestamp']) for d in history_data]
        populations = [d['population'] for d in history_data]
        
        # Dimensioni del canvas
        canvas_width = self.graph_canvas.winfo_width()
        canvas_height = self.graph_canvas.winfo_height()
        
        # Margini
        margin = 30
        x_start = margin
        x_end = canvas_width - margin
        y_start = canvas_height - margin
        y_end = margin
        
        # Scaling dei dati
        pop_min = min(populations)
        pop_max = max(populations)
        
        if pop_max == pop_min:
            pop_min -= 10
            pop_max += 10
        
        def scale_x(timestamp):
            total_span = (timestamps[-1] - timestamps[0]).total_seconds()
            if total_span == 0:
                return x_start
            time_offset = (timestamp - timestamps[0]).total_seconds()
            return x_start + (time_offset / total_span) * (x_end - x_start)

        def scale_y(population):
            pop_span = pop_max - pop_min
            if pop_span == 0:
                return y_start
            return y_start - ((population - pop_min) / pop_span) * (y_start - y_end)

        # Disegna gli assi
        self.graph_canvas.create_line(x_start, y_start, x_end, y_start, fill=TEXT_COLOR)
        self.graph_canvas.create_line(x_start, y_start, x_start, y_end, fill=TEXT_COLOR)

        # Disegna il grafico a linee
        points = []
        for i in range(len(populations)):
            x = scale_x(timestamps[i])
            y = scale_y(populations[i])
            points.append((x, y))
            
            # Disegna i punti
            self.graph_canvas.create_oval(x - 3, y - 3, x + 3, y + 3, fill=GRAPH_COLOR, outline="")
            
            # Aggiungi etichetta per il punto
            self.graph_canvas.create_text(x, y - 10, text=str(populations[i]),
                                          fill=TEXT_COLOR, font=("Segoe UI", 8))
            
        if points:
            self.graph_canvas.create_line(points, fill=GRAPH_COLOR, width=2, smooth=True)

        # Disegna etichette per gli assi
        self.graph_canvas.create_text(x_start, y_start + 15, text=timestamps[0].strftime("%d/%m"), fill=TEXT_COLOR)
        self.graph_canvas.create_text(x_end, y_start + 15, text=timestamps[-1].strftime("%d/%m"), fill=TEXT_COLOR)
        
        self.graph_canvas.create_text(x_start - 5, y_start, text=str(pop_min), anchor="e", fill=TEXT_COLOR)
        self.graph_canvas.create_text(x_start - 5, y_end, text=str(pop_max), anchor="e", fill=TEXT_COLOR)

    def _create_right_panel(self, parent):
        right_panel = tk.Frame(parent, bg=CARD_BG_COLOR)

        self.colony_notebook = ttk.Notebook(right_panel)
        self.colony_notebook.pack(fill="both", expand=True, padx=10, pady=10)

        gallery_tab = self._create_gallery_tab()
        notes_tab = self._create_notes_tab()

        self.colony_notebook.add(gallery_tab, text="📸 Galleria")
        self.colony_notebook.add(notes_tab, text="📝 Blocco Note")

        return right_panel

    def _create_gallery_tab(self):
        gallery_tab = tk.Frame(self.colony_notebook, bg=CARD_BG_COLOR)

        gallery_header = tk.Frame(gallery_tab, bg=CARD_BG_COLOR)
        gallery_header.pack(fill="x", padx=20, pady=(20, 10))

        tk.Label(gallery_header, text="📸 Galleria Immagini",
                font=("Segoe UI", 14, "bold"),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(side="left")

        ttk.Button(gallery_header, text="➕ Aggiungi Immagine",
                  style="Success.TButton",
                  command=self.add_colony_image).pack(side="right")

        gallery_canvas = tk.Canvas(gallery_tab, bg=DEFAULT_BG_COLOR, highlightthickness=0)
        gallery_scrollbar = ttk.Scrollbar(gallery_tab, orient="vertical", command=gallery_canvas.yview)
        self.gallery_frame = tk.Frame(gallery_canvas, bg=DEFAULT_BG_COLOR)

        self.gallery_frame.bind(
            "<Configure>",
            lambda e: gallery_canvas.configure(scrollregion=gallery_canvas.bbox("all"))
        )

        gallery_canvas.create_window((0, 0), window=self.gallery_frame, anchor="nw")
        gallery_canvas.configure(yscrollcommand=gallery_scrollbar.set)

        gallery_canvas.pack(side="left", fill="both", expand=True, padx=20, pady=(0, 20))
        gallery_scrollbar.pack(side="right", fill="y", padx=(0, 20), pady=(0, 20))

        self.display_colony_images()

        return gallery_tab

    def _create_notes_tab(self):
        notes_tab = tk.Frame(self.colony_notebook, bg=CARD_BG_COLOR)

        tk.Label(notes_tab, text="Appunti della Colonia",
                font=("Segoe UI", 14, "bold"),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", padx=20, pady=(20, 10))

        self.notes_text_area = scrolledtext.ScrolledText(notes_tab, wrap="word",
                                                        font=("Segoe UI", 10),
                                                        bg=DEFAULT_BG_COLOR, fg=TEXT_COLOR,
                                                        insertbackground=TEXT_COLOR)
        self.notes_text_area.insert(tk.END, self.current_colony.get("notes", ""))
        self.notes_text_area.pack(fill="both", expand=True, padx=20, pady=(0, 10))

        ttk.Button(notes_tab, text="Salva Appunti",
                  style="Success.TButton",
                  command=self.save_notes).pack(pady=5, padx=20, anchor="e")

        return notes_tab


    def show_dashboard(self):
        # Pulisci
        for widget in self.dashboard_container.winfo_children():
            widget.destroy()

        if not self.colonies:
            tk.Label(self.dashboard_container, text="Nessun dato da mostrare.", bg=DEFAULT_BG_COLOR, fg=TEXT_COLOR).pack(pady=50)
            return

        # 1. Statistiche Aggregre
        stats_frame = tk.Frame(self.dashboard_container, bg=DEFAULT_BG_COLOR)
        stats_frame.pack(fill="x", pady=20)
        
        total_colonies = len(self.colonies)
        total_ants = sum(c['history'][-1]['population'] for c in self.colonies if c.get('history'))
        
        # Trova top colonia
        top_colony = max(self.colonies, key=lambda c: c['history'][-1]['population'] if c.get('history') else 0)
        top_colyna_name = top_colony['name']
        top_colony_pop = top_colony['history'][-1]['population'] if top_colony.get('history') else 0
        
        def create_stat_card(parent, title, value, icon):
            card = tk.Frame(parent, bg=CARD_BG_COLOR, padx=20, pady=15)
            card.pack(side="left", fill="both", expand=True, padx=10)
            
            tk.Label(card, text=icon, font=("Segoe UI", 24), bg=CARD_BG_COLOR, fg=ACCENT_COLOR).pack()
            tk.Label(card, text=value, font=("Segoe UI", 20, "bold"), bg=CARD_BG_COLOR, fg=TEXT_COLOR).pack()
            tk.Label(card, text=title, font=("Segoe UI", 10), bg=CARD_BG_COLOR, fg="#bdc3c7").pack()

        create_stat_card(stats_frame, "Colonie Totali", str(total_colonies), "🏠")
        create_stat_card(stats_frame, "Formiche Totali", str(total_ants), "🐜")
        create_stat_card(stats_frame, "Colonia più grande", f"{top_colyna_name}\n({top_colony_pop})", "👑")

        # 2. Prossime Nutrizioni (Tutte)
        feed_frame = tk.Frame(self.dashboard_container, bg=CARD_BG_COLOR)
        feed_frame.pack(fill="both", expand=True, pady=10)
        
        tk.Label(feed_frame, text="📅 Prossime Attività (Tutte le colonie)", font=("Segoe UI", 14, "bold"), bg=CARD_BG_COLOR, fg=TEXT_COLOR).pack(anchor="w", padx=20, pady=15)
        
        # Raccogli tutti gli eventi
        all_events = []
        for colony in self.colonies:
            # Singoli
            for s in colony.get('feeding_schedule', []):
                try:
                    dt = datetime.fromisoformat(s['datetime'])
                    if dt > datetime.now():
                        all_events.append({
                            'dt': dt,
                            'colony': colony['name'],
                            'type': 'Singolo',
                            'desc': s.get('description', ''),
                            'food': s.get('food_type', 'Cibo')
                        })
                except: pass
            
            # Ricorrenti (prossima occorrenza)
            for r in colony.get('recurring_schedule', []):
                try:
                    start = datetime.fromisoformat(r['start_date']).date()
                    interval = r.get('interval', 7)
                    today = datetime.now().date()
                    
                    # Calcola prossima data
                    days_passed = (today - start).days
                    if days_passed < 0:
                        next_date = start
                    else:
                        cycles = days_passed // interval
                        next_date = start + timedelta(days=(cycles + 1) * interval)
                    
                    next_dt = datetime.combine(next_date, datetime.min.time())
                    
                    all_events.append({
                        'dt': next_dt,
                        'colony': colony['name'],
                        'type': 'Ricorrente',
                        'desc': f"Ogni {interval} giorni",
                        'food': r.get('food_type', 'Cibo')
                    })
                except: pass
        
        # Sort e prendi primi 10
        all_events.sort(key=lambda x: x['dt'])
        upcoming = all_events[:8]
        
        if not upcoming:
             tk.Label(feed_frame, text="Nessuna attività programmata.", bg=CARD_BG_COLOR, fg="#95a5a6").pack(pady=20)
        else:
            list_frame = tk.Frame(feed_frame, bg=CARD_BG_COLOR)
            list_frame.pack(fill="both", expand=True, padx=20)
            
            for ev in upcoming:
                 row = tk.Frame(list_frame, bg=DEFAULT_BG_COLOR, pady=5)
                 row.pack(fill="x", pady=2)
                 
                 date_str = ev['dt'].strftime("%d/%m")
                 tk.Label(row, text=f"[{date_str}]", font=("Segoe UI", 10, "bold"), fg=ACCENT_COLOR, bg=DEFAULT_BG_COLOR, width=8).pack(side="left", padx=5)
                 tk.Label(row, text=f"{ev['colony']}", font=("Segoe UI", 10, "bold"), fg=TEXT_COLOR, bg=DEFAULT_BG_COLOR, width=20, anchor="w").pack(side="left")
                 tk.Label(row, text=f"{ev['food']} ({ev['type']})", font=("Segoe UI", 10), fg="#bdc3c7", bg=DEFAULT_BG_COLOR).pack(side="left", padx=10)

    def show_settings(self):
        dialog = tk.Toplevel(self.root)
        dialog.title("Impostazioni")
        dialog.geometry("800x600")
        dialog.configure(bg=CARD_BG_COLOR)
        dialog.transient(self.root)
        dialog.grab_set()

        # Layout principale
        main_container = tk.Frame(dialog, bg=CARD_BG_COLOR)
        main_container.pack(fill="both", expand=True)

        # Sidebar (Sinistra)
        sidebar = tk.Frame(main_container, bg=DEFAULT_BG_COLOR, width=200)
        sidebar.pack(side="left", fill="y")
        sidebar.pack_propagate(False)

        # Content Area (Destra)
        content_area = tk.Frame(main_container, bg=CARD_BG_COLOR)
        content_area.pack(side="right", fill="both", expand=True)

        # Variabili di stato
        self._current_settings_frame = None
        
        # Variabili impostazioni
        self.notif_desktop_var = tk.BooleanVar(value=self.settings.get("notifications_desktop", True))
        self.notif_email_var = tk.BooleanVar(value=self.settings.get("notifications_email", False))
        self.email_sender_var = tk.StringVar(value=self.settings.get("email_sender", ""))
        self.email_password_var = tk.StringVar(value=self.settings.get("email_password", ""))
        self.email_recipient_var = tk.StringVar(value=self.settings.get("email_recipient", ""))
        self.smtp_server_var = tk.StringVar(value=self.settings.get("smtp_server", "smtp.gmail.com"))
        self.smtp_port_var = tk.StringVar(value=str(self.settings.get("smtp_port", 587)))
        self.update_url_var = tk.StringVar(value=self.settings.get("update_url", ""))

        # Stile pulsanti sidebar
        def create_sidebar_btn(text, command):
            btn = tk.Button(sidebar, text=text, font=("Segoe UI", 11),
                          fg=TEXT_COLOR, bg=DEFAULT_BG_COLOR,
                          activebackground=ACCENT_COLOR, activeforeground="white",
                          bd=0, anchor="w", padx=20, pady=10,
                          command=command)
            btn.pack(fill="x")
            return btn

        # Funzioni di navigazione
        def clear_content():
            if self._current_settings_frame:
                self._current_settings_frame.destroy()

        def show_general():
            clear_content()
            frame = tk.Frame(content_area, bg=CARD_BG_COLOR)
            frame.pack(fill="both", expand=True, padx=30, pady=30)
            self._current_settings_frame = frame

            tk.Label(frame, text="Generale", font=("Segoe UI", 18, "bold"), fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", pady=(0, 20))

            # Backup
            bk_group = tk.LabelFrame(frame, text="Backup & Ripristino", font=("Segoe UI", 11, "bold"), fg=TEXT_COLOR, bg=CARD_BG_COLOR, bd=1, relief="solid")
            bk_group.pack(fill="x", pady=10, ipady=10)
            
            tk.Label(bk_group, text="Gestisci i salvataggi dei tuoi dati.", font=("Segoe UI", 10), fg="#bdc3c7", bg=CARD_BG_COLOR).pack(anchor="w", padx=20, pady=5)
            
            btn_frame = tk.Frame(bk_group, bg=CARD_BG_COLOR)
            btn_frame.pack(fill="x", padx=20, pady=10)
            ttk.Button(btn_frame, text="Crea Backup Ora", style="Modern.TButton", command=lambda: self.create_backup(silent=False)).pack(side="left", padx=(0, 10))
            ttk.Button(btn_frame, text="Ripristina Backup", style="Warning.TButton", command=self.restore_backup).pack(side="left")

        def show_notifications():
            clear_content()
            frame = tk.Frame(content_area, bg=CARD_BG_COLOR)
            frame.pack(fill="both", expand=True, padx=30, pady=30)
            self._current_settings_frame = frame

            tk.Label(frame, text="Notifiche", font=("Segoe UI", 18, "bold"), fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", pady=(0, 20))

            # Toggles
            tk.Label(frame, text="Preferenze di notifica", font=("Segoe UI", 12, "bold"), fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", pady=(10, 5))
            
            # Use default style for clear checkbox state
            ttk.Checkbutton(frame, text="🔔 Notifiche Desktop (Popup di Windows)", variable=self.notif_desktop_var).pack(anchor="w", padx=10, pady=5)
            ttk.Checkbutton(frame, text="📧 Notifiche Email", variable=self.notif_email_var).pack(anchor="w", padx=10, pady=5)

            # Email Config
            email_group = tk.LabelFrame(frame, text="Configurazione Email (SMTP)", font=("Segoe UI", 11, "bold"), fg=TEXT_COLOR, bg=CARD_BG_COLOR, bd=1, relief="solid")
            email_group.pack(fill="x", pady=20, ipady=10)

            grid_frame = tk.Frame(email_group, bg=CARD_BG_COLOR)
            grid_frame.pack(padx=20, pady=10)

            # Campi Email
            fields = [
                ("Email Mittente:", self.email_sender_var),
                ("Password App:", self.email_password_var),
                ("Email Destinarario:", self.email_recipient_var),
                ("Server SMTP:", self.smtp_server_var),
                ("Porta:", self.smtp_port_var)
            ]

            for i, (label_text, var) in enumerate(fields):
                tk.Label(grid_frame, text=label_text, fg=TEXT_COLOR, bg=CARD_BG_COLOR).grid(row=i, column=0, sticky="w", pady=5)
                entry = tk.Entry(grid_frame, textvariable=var, width=30)
                if "Password" in label_text: entry.configure(show="*")
                entry.grid(row=i, column=1, sticky="w", padx=10)

            ttk.Button(email_group, text="Test Connessione", style="Modern.TButton", command=self.test_email_connection).pack(anchor="w", padx=20, pady=10)

        def show_info():
            clear_content()
            frame = tk.Frame(content_area, bg=CARD_BG_COLOR)
            frame.pack(fill="both", expand=True, padx=30, pady=30)
            self._current_settings_frame = frame

            tk.Label(frame, text="Info & Aggiornamenti", font=("Segoe UI", 18, "bold"), fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", pady=(0, 20))

            info_container = tk.Frame(frame, bg=CARD_BG_COLOR)
            info_container.pack(fill="x", pady=10)
            
            tk.Label(info_container, text="Ant Colony Monitor", font=("Segoe UI", 16, "bold"), fg=ACCENT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w")
            tk.Label(info_container, text=f"Versione: {CURRENT_VERSION}", font=("Segoe UI", 12), fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w")

            # Updates
            upd_group = tk.LabelFrame(frame, text="Aggiornamenti Software", font=("Segoe UI", 11, "bold"), fg=TEXT_COLOR, bg=CARD_BG_COLOR, bd=1, relief="solid")
            upd_group.pack(fill="x", pady=20, ipady=10)

            tk.Label(upd_group, text="URL Repository:", fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", padx=20, pady=(10,0))
            tk.Entry(upd_group, textvariable=self.update_url_var, width=50).pack(fill="x", padx=20, pady=5)
            tk.Label(upd_group, text="URL del file 'raw' su GitHub", font=("Segoe UI", 8), fg="#95a5a6", bg=CARD_BG_COLOR).pack(anchor="w", padx=20)
            
            ttk.Button(upd_group, text="Cerca Aggiornamenti", style="Success.TButton", command=self.check_for_updates).pack(anchor="w", padx=20, pady=15)

        # Pulsanti Sidebar
        tk.Label(sidebar, text="IMPOSTAZIONI", font=("Segoe UI", 12, "bold"), fg="#bdc3c7", bg=DEFAULT_BG_COLOR).pack(pady=(20, 10))
        create_sidebar_btn("🏠 Generale", show_general)
        create_sidebar_btn("🔔 Notifiche", show_notifications)
        create_sidebar_btn("ℹ️ Info", show_info)

        # Footer con pulsanti azione
        footer = tk.Frame(content_area, bg=DEFAULT_BG_COLOR, height=60)
        footer.pack(side="bottom", fill="x")
        footer.pack_propagate(False)

        def save_and_close():
            self.settings["notifications_email"] = self.notif_email_var.get()
            self.settings["notifications_desktop"] = self.notif_desktop_var.get()
            self.settings["email_sender"] = self.email_sender_var.get().strip()
            self.settings["email_password"] = self.email_password_var.get().strip()
            self.settings["email_recipient"] = self.email_recipient_var.get().strip()
            self.settings["smtp_server"] = self.smtp_server_var.get().strip()
            self.settings["update_url"] = self.update_url_var.get().strip()
            try:
                self.settings["smtp_port"] = int(self.smtp_port_var.get().strip())
            except ValueError:
                messagebox.showerror("Errore", "La porta SMTP deve essere un numero intero.")
                return

            self.save_data()
            dialog.destroy()
            messagebox.showinfo("Successo", "Impostazioni salvate con successo!")
            self.restart_notification_thread()

        btn_box = tk.Frame(footer, bg=DEFAULT_BG_COLOR)
        btn_box.pack(side="right", padx=20, pady=10)
        
        ttk.Button(btn_box, text="Salva e Chiudi", style="Success.TButton", command=save_and_close).pack(side="left", padx=5)
        ttk.Button(btn_box, text="Annulla", style="Danger.TButton", command=dialog.destroy).pack(side="left", padx=5)

        # Mostra schermata iniziale
        show_general()

    def check_for_updates(self):
        url = self.update_url_var.get().strip()
        if not url:
            messagebox.showerror("Errore", "Inserisci un URL valido per l'aggiornamento.")
            return
            
        try:
            import urllib.request
            
            # Scarica il file remoto
            try:
                with urllib.request.urlopen(url) as response:
                    remote_code = response.read()
            except Exception as dl_err:
                messagebox.showerror("Errore Download", f"Impossibile scaricare dal server:\n{dl_err}")
                return

            local_code = ""
            with open(__file__, "rb") as f:
                local_code = f.read()
                
            # Normalize line endings for comparison just in case
            if remote_code.replace(b'\r\n', b'\n') == local_code.replace(b'\r\n', b'\n'):
                messagebox.showinfo("Aggiornamento", "Nessun aggiornamento disponibile. Hai l'ultima versione.")
                return
                
            if messagebox.askyesno("Aggiornamento Disponibile", "È stata trovata una nuova versione. Vuoi aggiornare ora?\n\nL'applicazione verrà riavviata."):
                self.perform_update(remote_code)
                
        except Exception as e:
            messagebox.showerror("Errore", f"Impossibile controllare aggiornamenti:\n{e}")

    def perform_update(self, new_code):
        try:
            import sys
            import subprocess
            
            # Scrivi il nuovo codice in un file temporaneo
            new_file = "app_update.new"
            with open(new_file, "wb") as f:
                f.write(new_code)
                
            # Crea script batch per sostituire il file e riavviare
            current_script = os.path.abspath(__file__)
            batch_script = "update.bat"
            
            with open(batch_script, "w") as f:
                f.write(f"@echo off\n")
                f.write(f"timeout /t 2 >nul\n") # Aspetta che l'app si chiuda
                f.write(f"move /y \"{new_file}\" \"{current_script}\"\n")
                f.write(f"start python \"{current_script}\"\n")
                f.write(f"del \"%~f0\"\n") # Autodistruzione script
                
            # Avvia lo script e chiudi l'app
            subprocess.Popen(batch_script, shell=True)
            self.root.destroy()
            sys.exit()
            
        except Exception as e:
             messagebox.showerror("Errore Aggiornamento", f"Errore durante l'aggiornamento:\n{e}")

    def test_email_connection(self):
        sender_email = self.email_sender_var.get().strip()
        password = self.email_password_var.get().strip()
        recipient_email = self.email_recipient_var.get().strip()
        smtp_server = self.smtp_server_var.get().strip()
        
        try:
            port = int(self.smtp_port_var.get().strip())
        except ValueError:
            messagebox.showerror("Errore", "La porta SMTP deve essere un numero intero.")
            return

        if not all([sender_email, password, recipient_email, smtp_server, port]):
            messagebox.showerror("Errore", "Tutti i campi per l'email devono essere compilati.")
            return

        subject = "Test Email Ant Colony Monitor"
        body = f"Ciao! Questa è un'email di prova inviata da Ant Colony Monitor.\nSe ricevi questo messaggio, la tua configurazione email è corretta."
        
        try:
            context = ssl.create_default_context()
            if port == 465:
                # Usa SSL diretto per la porta 465
                with smtplib.SMTP_SSL(smtp_server, port, context=context) as server:
                    server.login(sender_email, password)
                    message = f"Subject: {subject}\n\n{body}"
                    server.sendmail(sender_email, recipient_email, message.encode('utf-8'))
            else:
                # Usa STARTTLS per altre porte (es. 587)
                with smtplib.SMTP(smtp_server, port) as server:
                    server.starttls(context=context)
                    server.login(sender_email, password)
                    message = f"Subject: {subject}\n\n{body}"
                    server.sendmail(sender_email, recipient_email, message.encode('utf-8'))

            messagebox.showinfo("Successo", "Email di prova inviata con successo!")
        except smtplib.SMTPAuthenticationError:
            messagebox.showerror("Errore", "Errore di autenticazione. Controlla email e password.")
        except Exception as e:
            messagebox.showerror("Errore", f"Impossibile inviare l'email: {e}")

    def create_backup(self, silent=False):
        if not os.path.exists(BACKUP_DIR):
            os.makedirs(BACKUP_DIR)
        
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        backup_file = os.path.join(BACKUP_DIR, f"backup_{timestamp}.json")
        
        try:
            shutil.copy(DATA_FILE, backup_file)
            # Mantieni solo gli ultimi 5 backup
            backups = sorted([f for f in os.listdir(BACKUP_DIR) if f.startswith("backup_")], reverse=True)
            for old_backup in backups[5:]:
                os.remove(os.path.join(BACKUP_DIR, old_backup))
            if not silent:
                messagebox.showinfo("Backup", "Backup creato con successo!")
            else:
                logger.info("Backup automatico creato")
        except Exception as e:
            if not silent:
                messagebox.showerror("Errore", f"Errore durante il backup: {e}")
            else:
                logger.error(f"Errore durante backup automatico: {e}")

    def restore_backup(self):
        if not os.path.exists(BACKUP_DIR):
            messagebox.showinfo("Info", "Nessun backup disponibile")
            return
            
        backups = sorted([f for f in os.listdir(BACKUP_DIR) if f.startswith("backup_")], reverse=True)
        
        if not backups:
            messagebox.showinfo("Info", "Nessun backup disponibile")
            return
            
        dialog = tk.Toplevel(self.root)
        dialog.title("Ripristina Backup")
        dialog.geometry("400x300")
        dialog.configure(bg=CARD_BG_COLOR)
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.focus_set()
        
        content = tk.Frame(dialog, bg=CARD_BG_COLOR)
        content.pack(fill="both", expand=True, padx=20, pady=20)
        
        tk.Label(content, text="Seleziona un backup:",
                font=("Segoe UI", 12),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(pady=(0, 10))
        
        backup_list = tk.Listbox(content, bg=DEFAULT_BG_COLOR, fg=TEXT_COLOR,
                               selectbackground=ACCENT_COLOR, font=("Segoe UI", 10))
        for backup in backups:
            date_str = backup[7:15] + " " + backup[16:22]
            backup_list.insert(tk.END, date_str)
        backup_list.pack(fill="both", expand=True, pady=10)
        
        def restore_selected():
            selected = backup_list.curselection()
            if not selected:
                return
                
            backup_file = os.path.join(BACKUP_DIR, backups[selected[0]])
            if messagebox.askyesno("Conferma Ripristino", 
                                  "Sei sicuro di voler ripristinare questo backup? Tutti i dati attuali non salvati verranno persi."):
                try:
                    # Basic validation
                    if os.path.getsize(backup_file) == 0:
                        raise ValueError("Il file di backup è vuoto")

                    # Verify it's a valid JSON structure before overwriting
                    with open(backup_file, 'r', encoding='utf-8') as f:
                        test_load = json.load(f)
                        if not isinstance(test_load, dict):
                            raise ValueError("Il backup non ha il formato corretto (deve essere un dizionario).")

                    shutil.copy(backup_file, DATA_FILE)
                    self.colonies, self.settings = self.load_data()
                    dialog.destroy()
                    self.create_main_frame()
                    messagebox.showinfo("Successo", "Backup ripristinato con successo!")
                except json.JSONDecodeError:
                    messagebox.showerror("Errore", "Il file di backup è corrotto (JSON non valido).")
                except Exception as e:
                    messagebox.showerror("Errore", f"Errore durante il ripristino: {str(e)}")
        
        btn_frame = tk.Frame(content, bg=CARD_BG_COLOR)
        btn_frame.pack(fill="x", pady=10)
        
        ttk.Button(btn_frame, text="Ripristina",
                  style="Success.TButton",
                  command=restore_selected).pack(side="right", padx=5)
        
        ttk.Button(btn_frame, text="Annulla",
                  style="Modern.TButton",
                  command=dialog.destroy).pack(side="right", padx=5)

    def on_window_resize(self, event):
        if event.widget == self.root:
            current_size = (event.width, event.height)
            if current_size != self.last_size and any(current_size):
                self.last_size = current_size
                self.update_background_image()
                if not self.current_colony and hasattr(self, 'canvas') and self.canvas.winfo_exists():
                    current_width = self.canvas.winfo_width() or event.width
                    new_num_columns = max(1, current_width // 290)
                    if new_num_columns != self.last_colony_grid_width:
                        self.display_colonies()
                if self.current_colony and hasattr(self, 'graph_canvas') and self.graph_canvas.winfo_exists():
                    self.draw_population_graph()

    def set_background_image(self):
        file_path = filedialog.askopenfilename(
            filetypes=[("Image files", "*.jpg *.jpeg *.png *.gif *.bmp")]
        )
        if file_path:
            self.background_image_path = file_path
            self.settings["background_image_path"] = file_path
            self.save_data()
            self.create_main_frame() # Ricrea l'interfaccia per applicare la trasparenza

    def update_background_image(self):
         # L'immagine viene disegnata direttamente nel metodo display_colonies (sul canvas).
         # Qui aggiorniamo solo l'interfaccia se necessario.
         if hasattr(self, 'canvas') and self.canvas.winfo_exists():
             self.display_colonies()
    
    def clear_frame(self):
        for widget in self.root.winfo_children():
            if widget is not self._current_background_label:
                widget.destroy()

    def show_calendar(self):
        self.clear_frame()
        self.current_colony = None # Resetta la colonia attuale

        main_container = tk.Frame(self.root, bg=self.bg_color)
        main_container.pack(fill="both", expand=True)

        header = tk.Frame(main_container, bg=CARD_BG_COLOR, height=80)
        header.pack(fill="x")
        header.pack_propagate(False)

        header_content = tk.Frame(header, bg=CARD_BG_COLOR)
        header_content.pack(fill="both", expand=True, padx=20, pady=15)

        ttk.Button(header_content, text="← Indietro",
                  style="Modern.TButton",
                  command=self.create_main_frame).pack(side="left")

        tk.Label(header_content,
                text="📅 Calendario Alimentazione",
                font=("Segoe UI", 18, "bold"),
                fg=TEXT_COLOR,
                bg=CARD_BG_COLOR).pack(side="left", padx=20)

        calendar_frame = tk.Frame(main_container, bg=DEFAULT_BG_COLOR)
        calendar_frame.pack(fill="both", expand=True, padx=20, pady=20)

        self._create_calendar_view(calendar_frame)

    def _create_calendar_view(self, parent):
        top_frame = tk.Frame(parent, bg=CARD_BG_COLOR)
        top_frame.pack(fill="x", pady=(0, 10), padx=10)

        # Pulsanti di navigazione
        ttk.Button(top_frame, text="<", style="Modern.TButton",
                   command=self._prev_month).pack(side="left", padx=5)

        self.month_year_label = tk.Label(top_frame, text="",
                                        font=("Segoe UI", 16, "bold"),
                                        fg=TEXT_COLOR, bg=CARD_BG_COLOR)
        self.month_year_label.pack(side="left", expand=True)

        ttk.Button(top_frame, text=">", style="Modern.TButton",
                   command=self._next_month).pack(side="left", padx=5)
        
        self.calendar_grid_frame = tk.Frame(parent, bg=self.bg_color)
        self.calendar_grid_frame.pack(fill="both", expand=True)
        
        self.events_frame = tk.Frame(parent, bg=CARD_BG_COLOR)
        self.events_frame.pack(fill="both", expand=True, padx=10, pady=10)

        self.update_calendar_view()
        
    def update_calendar_view(self):
        # Pulisci il vecchio calendario
        for widget in self.calendar_grid_frame.winfo_children():
            widget.destroy()
        
        # Pulisci gli eventi
        for widget in self.events_frame.winfo_children():
            widget.destroy()

        # Aggiorna l'etichetta mese/anno
        self.month_year_label.config(text=self.current_calendar_date.strftime("%B %Y"))
        
        # Titoli dei giorni della settimana
        day_names = ["Lunedì", "Martedì", "Mercoledì", "Giovedì", "Venerdì", "Sabato", "Domenica"]
        for i, day in enumerate(day_names):
            tk.Label(self.calendar_grid_frame, text=day,
                    font=("Segoe UI", 10, "bold"), fg=TEXT_COLOR, bg=CARD_BG_COLOR,
                    width=12, height=2).grid(row=0, column=i, sticky="nsew", padx=1, pady=1)

        # Dati del calendario
        cal = calendar.Calendar()
        month_days = cal.monthdatescalendar(self.current_calendar_date.year, self.current_calendar_date.month)

        all_feeding_dates = self.get_all_feeding_dates()
        
        row_idx = 1
        for week in month_days:
            for col_idx, day_date in enumerate(week):
                day_frame = tk.Frame(self.calendar_grid_frame,
                                     bg=CARD_BG_COLOR,
                                     relief="raised", bd=1)
                day_frame.grid(row=row_idx, column=col_idx, sticky="nsew", padx=1, pady=1)
                
                # Sfondo per evidenziare i promemoria
                bg_color = CARD_BG_COLOR
                if day_date in all_feeding_dates:
                    bg_color = ACCENT_COLOR # Giorno con promemoria

                if day_date.month != self.current_calendar_date.month:
                    fg_color = "#5d6d7e" # Giorni del mese precedente/successivo
                else:
                    fg_color = TEXT_COLOR
                
                day_frame.config(bg=bg_color)

                day_label = tk.Label(day_frame, text=day_date.day,
                                     font=("Segoe UI", 12),
                                     fg=fg_color, bg=bg_color)
                day_label.pack(anchor="ne", padx=5, pady=5)
                
                # Aggiungi un piccolo punto se ci sono promemoria
                if bg_color == ACCENT_COLOR:
                     event_label = tk.Label(day_frame, text="•", font=("Segoe UI", 20, "bold"), fg=TEXT_COLOR, bg=bg_color)
                     event_label.pack(side="bottom", anchor="s", expand=True)

                if day_date.month == self.current_calendar_date.month:
                    day_frame.bind("<Button-1>", lambda e, d=day_date: self._show_day_events(d))
                    day_label.bind("<Button-1>", lambda e, d=day_date: self._show_day_events(d))

            row_idx += 1
            
        # Pesa le righe e le colonne per l'espansione
        for i in range(7):
            self.calendar_grid_frame.grid_columnconfigure(i, weight=1)
        for i in range(1, row_idx):
            self.calendar_grid_frame.grid_rowconfigure(i, weight=1)

    def _show_day_events(self, day_date):
        for widget in self.events_frame.winfo_children():
            widget.destroy()

        day_str = day_date.strftime("%Y-%m-%d")
        
        tk.Label(self.events_frame, text=f"Promemoria per il {day_str}",
                font=("Segoe UI", 14, "bold"),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", padx=10, pady=(10, 5))

        found_events = False
        for colony in self.colonies:
            colony_name = colony['name']
            
            # Promemoria singoli
            for schedule_dict in sorted(colony.get("feeding_schedule", []), key=lambda x: x['datetime']):
                try:
                    schedule_str = schedule_dict['datetime']
                    if schedule_str.startswith(day_str):
                        found_events = True
                        event_dt = datetime.fromisoformat(schedule_str)
                        food_type = schedule_dict.get('food_type', 'N/D')
                        quantity = schedule_dict.get('quantity', 'N/D')
                        description = schedule_dict.get('description', '')
                        
                        event_text = f"🍯 {event_dt.strftime('%H:%M')} - {colony_name}\n"
                        event_text += f"Tipo: {food_type} ({quantity})"
                        if description:
                            event_text += f"\nNote: {description}"
                        
                        event_frame = tk.Frame(self.events_frame, bg=DEFAULT_BG_COLOR)
                        event_frame.pack(fill="x", padx=10, pady=2)
                        
                        tk.Label(event_frame, text=event_text,
                                font=("Segoe UI", 10),
                                fg=TEXT_COLOR, bg=DEFAULT_BG_COLOR, justify="left").pack(side="left")
                                
                        ttk.Button(event_frame, text="🗑️", style="Danger.TButton",
                                  command=lambda c=colony, s=schedule_dict: self._delete_calendar_event(c, s, is_recurring=False)).pack(side="right")
                except (ValueError, KeyError):
                    pass

        if not found_events:
            tk.Label(self.events_frame, text="Nessun promemoria in questo giorno.",
                    font=("Segoe UI", 10, "italic"),
                    fg="#95a5a6", bg=CARD_BG_COLOR).pack(padx=10, pady=10)
        
        add_frame = tk.Frame(self.events_frame, bg=CARD_BG_COLOR)
        add_frame.pack(fill="x", padx=10, pady=(10, 0))
        
        ttk.Button(add_frame, text="➕ Aggiungi Promemoria", style="Success.TButton",
                   command=lambda d=day_date: self._add_event_dialog(d)).pack(side="right", pady=5)
    
    def _delete_calendar_event(self, colony, schedule_dict, is_recurring):
        if messagebox.askyesno("Elimina Promemoria", "Sei sicuro di voler eliminare questo promemoria?"):
            if is_recurring:
                colony['recurring_schedule'].remove(schedule_dict)
            else:
                colony['feeding_schedule'].remove(schedule_dict)
            self.save_data()
            self.update_calendar_view()
            messagebox.showinfo("Successo", "Promemoria eliminato!")

    def _add_event_dialog(self, day_date):
        dialog = tk.Toplevel(self.root)
        dialog.title("Aggiungi Promemoria")
        dialog.geometry("350x450")
        dialog.configure(bg=CARD_BG_COLOR)
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.focus_set()
        
        content = tk.Frame(dialog, bg=CARD_BG_COLOR)
        content.pack(fill="both", expand=True, padx=20, pady=20)
        
        tk.Label(content, text=f"Promemoria per il {day_date.strftime('%d-%m-%Y')}",
                font=("Segoe UI", 14, "bold"),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(pady=(0, 10))
        
        tk.Label(content, text="Seleziona Colonia:",
                font=("Segoe UI", 10),
                fg="#bdc3c7", bg=CARD_BG_COLOR).pack(anchor="w")
        
        colony_names = [c['name'] for c in self.colonies]
        if not colony_names:
            tk.Label(content, text="Nessuna colonia disponibile.", fg="red", bg=CARD_BG_COLOR).pack()
            return
            
        colony_var = tk.StringVar(value=colony_names[0])
        colony_menu = ttk.OptionMenu(content, colony_var, colony_names[0], *colony_names)
        colony_menu.pack(fill="x", pady=(0, 10))
        
        time_frame = tk.Frame(content, bg=CARD_BG_COLOR)
        time_frame.pack(fill="x", pady=5)
        
        tk.Label(time_frame, text="Orario:",
                font=("Segoe UI", 10),
                fg="#bdc3c7", bg=CARD_BG_COLOR).pack(side="left")
        
        hour_var = tk.StringVar(value=datetime.now().strftime("%H"))
        hour_spin = tk.Spinbox(time_frame, from_=0, to=23, width=3, textvariable=hour_var,
                              font=("Segoe UI", 10))
        hour_spin.pack(side="left", padx=(10, 5))
        
        tk.Label(time_frame, text=":",
                font=("Segoe UI", 12, "bold"),
                fg="#bdc3c7", bg=CARD_BG_COLOR).pack(side="left")
        
        minute_var = tk.StringVar(value=datetime.now().strftime("%M"))
        minute_spin = tk.Spinbox(time_frame, from_=0, to=59, width=3, textvariable=minute_var,
                                font=("Segoe UI", 10))
        minute_spin.pack(side="left", padx=(5, 10))

        tk.Label(content, text="Tipo Cibo:", font=("Segoe UI", 10), fg="#bdc3c7", bg=CARD_BG_COLOR).pack(anchor="w", pady=5)
        food_type_var = ttk.Combobox(content, values=["Proteine", "Zucchero", "Insetto", "Miele", "Acqua", "Altro"], state="readonly")
        food_type_var.set("Proteine")
        food_type_var.pack(fill="x", pady=(0, 10))

        tk.Label(content, text="Quantità:", font=("Segoe UI", 10), fg="#bdc3c7", bg=CARD_BG_COLOR).pack(anchor="w", pady=5)
        quantity_entry = tk.Entry(content, width=15)
        quantity_entry.pack(fill="x", pady=(0, 10))

        tk.Label(content, text="Descrizione:",
                font=("Segoe UI", 10),
                fg="#bdc3c7", bg=CARD_BG_COLOR).pack(anchor="w", pady=(5, 0))

        description_text = scrolledtext.ScrolledText(content, wrap="word", width=30, height=3,
                                                    font=("Segoe UI", 10),
                                                    bg=DEFAULT_BG_COLOR, fg=TEXT_COLOR,
                                                    insertbackground=TEXT_COLOR)
        description_text.pack(fill="x", pady=(0, 10))

        def save_event():
            selected_colony_name = colony_var.get()
            selected_colony = next((c for c in self.colonies if c['name'] == selected_colony_name), None)
            
            if selected_colony:
                try:
                    time_str = f"{hour_var.get().zfill(2)}:{minute_var.get().zfill(2)}"
                    description = description_text.get("1.0", tk.END).strip()
                    food_type = food_type_var.get()
                    quantity = quantity_entry.get()
                    datetime_obj = datetime.strptime(f"{day_date.strftime('%Y-%m-%d')} {time_str}", "%Y-%m-%d %H:%M")
                    new_schedule = {
                        "datetime": datetime_obj.isoformat(),
                        "description": description,
                        "food_type": food_type,
                        "quantity": quantity
                    }
                    selected_colony["feeding_schedule"].append(new_schedule)
                    self.save_data()
                    self.update_calendar_view()
                    dialog.destroy()
                    messagebox.showinfo("Successo", "Promemoria aggiunto con successo!")
                except ValueError:
                    messagebox.showerror("Errore", "Formato data/ora non valido.")
        
        btn_frame = tk.Frame(content, bg=CARD_BG_COLOR)
        btn_frame.pack(fill="x", pady=20)
        
        ttk.Button(btn_frame, text="Salva", style="Success.TButton", command=save_event).pack(side="right")
        ttk.Button(btn_frame, text="Annulla", style="Modern.TButton", command=dialog.destroy).pack(side="right", padx=5)

    def _prev_month(self):
        self.current_calendar_date = self.current_calendar_date.replace(day=1) - timedelta(days=1)
        self.current_calendar_date = self.current_calendar_date.replace(day=1)
        self.update_calendar_view()

    def _next_month(self):
        current_month = self.current_calendar_date.month
        current_year = self.current_calendar_date.year
        if current_month == 12:
            new_month = 1
            new_year = current_year + 1
        else:
            new_month = current_month + 1
            new_year = current_year
        self.current_calendar_date = self.current_calendar_date.replace(year=new_year, month=new_month, day=1)
        self.update_calendar_view()

    def get_all_feeding_dates(self):
        dates = set()
        today = datetime.now().date()

        for colony in self.colonies:
            # Promemoria singoli
            for schedule in colony.get("feeding_schedule", []):
                try:
                    date_part = datetime.fromisoformat(schedule['datetime']).date()
                    dates.add(date_part)
                except (KeyError, ValueError):
                    pass
            
            # Promemoria ricorrenti
            for recurring in colony.get("recurring_schedule", []):
                try:
                    start_date = datetime.fromisoformat(recurring['start_date']).date()
                    interval = recurring['interval']
                    
                    # Skip invalid intervals to prevent infinite loop
                    if interval <= 0:
                        continue
                    
                    if today >= start_date:
                        days_since_start = (today - start_date).days
                        if days_since_start % interval == 0:
                            dates.add(today)
                        
                        # Aggiungi anche gli eventi futuri nel mese corrente
                        # Calculate end of current calendar month to prevent infinite loop
                        end_of_month = self.current_calendar_date.replace(day=28) + timedelta(days=4)
                        end_of_month = end_of_month.replace(day=1)  # First day of next month
                        current_date = start_date
                        while current_date < end_of_month:
                            if current_date.month == self.current_calendar_date.month and current_date.year == self.current_calendar_date.year:
                                dates.add(current_date)
                            current_date += timedelta(days=interval)
                        
                except (KeyError, ValueError):
                    pass
        return dates

    def delete_colony(self, colony):
        if messagebox.askyesno("Elimina Colonia", f"Sei sicuro di voler eliminare la colonia '{colony['name']}'?"):
            self.colonies.remove(colony)
            self.save_data()
            
            # Se non ci sono più colonie, ricrea l'interfaccia principale per mostrare il placeholder
            if not self.colonies:
                self.create_main_frame()
            else:
                self.display_colonies()
                
            messagebox.showinfo("Successo", "Colonia eliminata con successo!")

    def save_description(self):
        new_description = self.description_text_area.get("1.0", tk.END).strip()
        self.current_colony["description"] = new_description
        self.save_data()
        messagebox.showinfo("Successo", "Descrizione salvata!")

    def update_profile_image(self):
        img_path = self.current_colony.get("profile_image", "")
        if img_path and os.path.exists(img_path):
            try:
                img = Image.open(img_path)
                img.thumbnail((200, 200), Image.Resampling.LANCZOS)
                photo = ImageTk.PhotoImage(img)
                self.profile_img_label.config(image=photo)
                self.profile_img_label.image = photo
            except (IOError, OSError):
                self.profile_img_label.config(image='', text="🐜\nNessuna\nImmagine", font=("Segoe UI", 12), fg="#95a5a6", bg=DEFAULT_BG_COLOR)
        else:
            self.profile_img_label.config(image='', text="🐜\nNessuna\nImmagine", font=("Segoe UI", 12), fg="#95a5a6", bg=DEFAULT_BG_COLOR)

    def change_profile_image(self):
        file_path = filedialog.askopenfilename(
            filetypes=[("Image files", "*.jpg *.jpeg *.png *.gif *.bmp")]
        )
        if file_path:
            if not os.path.exists(IMAGE_DIR):
                os.makedirs(IMAGE_DIR)
            
            file_name = os.path.basename(file_path)
            destination = os.path.join(IMAGE_DIR, f"{self.current_colony['name']}_profile_{file_name}")
            shutil.copy(file_path, destination)
            
            self.current_colony["profile_image"] = destination
            self.save_data()
            self.update_profile_image()

    def add_colony_image(self):
        file_path = filedialog.askopenfilename(
            filetypes=[("Image files", "*.jpg *.jpeg *.png *.gif *.bmp")]
        )
        if file_path:
            if not os.path.exists(IMAGE_DIR):
                os.makedirs(IMAGE_DIR)
            
            file_name = os.path.basename(file_path)
            destination = os.path.join(IMAGE_DIR, f"{self.current_colony['name']}_gallery_{len(self.current_colony['images'])}_{file_name}")
            shutil.copy(file_path, destination)
            
            self.current_colony["images"].append(destination)
            self.save_data()
            self.display_colony_images()

    def display_colony_images(self):
        for widget in self.gallery_frame.winfo_children():
            widget.destroy()

        images = self.current_colony.get("images", [])
        if not images:
            tk.Label(self.gallery_frame, text="Nessuna immagine nella galleria",
                    font=("Segoe UI", 12, "italic"),
                    fg="#95a5a6", bg=DEFAULT_BG_COLOR).pack(pady=20, fill="both", expand=True)
            return
        
        num_columns = 3
        
        for idx, img_path in enumerate(images):
            if os.path.exists(img_path):
                row = idx // num_columns
                col = idx % num_columns
                
                try:
                    img = Image.open(img_path)
                    img.thumbnail((150, 150), Image.Resampling.LANCZOS)
                    photo = ImageTk.PhotoImage(img)
                    
                    frame = tk.Frame(self.gallery_frame, bg=CARD_BG_COLOR)
                    frame.grid(row=row, column=col, padx=10, pady=10)
                    
                    img_label = tk.Label(frame, image=photo)
                    img_label.image = photo
                    img_label.pack()
                    
                    delete_btn = ttk.Button(frame, text="🗑️", style="Danger.TButton",
                                           command=lambda path=img_path: self.delete_gallery_image(path))
                    delete_btn.pack(pady=5)
                
                except (IOError, OSError):
                    pass

    def delete_gallery_image(self, img_path):
        if img_path in self.current_colony["images"]:
            if messagebox.askyesno("Elimina Immagine", "Sei sicuro di voler eliminare questa immagine?"):
                self.current_colony["images"].remove(img_path)
                if os.path.exists(img_path):
                    os.remove(img_path)
                self.save_data()
                self.display_colony_images()
    
    def save_notes(self):
        new_notes = self.notes_text_area.get("1.0", tk.END).strip()
        self.current_colony["notes"] = new_notes
        self.save_data()
        messagebox.showinfo("Successo", "Appunti salvati!")

    def start_notification_thread(self):
        # Evita di avviare più thread
        if self.notification_thread_running:
            return
        
        if self.settings.get("notifications_email") or (self.settings.get("notifications_desktop") and NOTIFICATIONS_AVAILABLE):
             self.notification_thread_running = True
             threading.Thread(target=self._check_notifications, daemon=True).start()
             logger.info("Thread di notifica avviato.")
        else:
            logger.info("Notifiche disabilitate nelle impostazioni.")

    def restart_notification_thread(self):
        self.notification_thread_running = False
        # Use after() to avoid blocking main thread
        self.root.after(1000, self.start_notification_thread)

    def _check_notifications(self):
        while self.notification_thread_running:
            now = datetime.now()
            today = now.date()
            logger.debug(f"Controllo notifiche... Ora attuale: {now.strftime('%H:%M:%S')}")
            
            for colony in self.colonies:
                # Gestisci i promemoria ricorrenti
                for recurring in list(colony.get("recurring_schedule", [])):
                    try:
                        start_date = datetime.fromisoformat(recurring['start_date']).date()
                        interval = recurring['interval']
                        
                        # Skip invalid intervals to prevent modulo by zero
                        if interval <= 0:
                            continue

                        if today >= start_date:
                            days_since_start = (today - start_date).days
                            if days_since_start % interval == 0:
                                # Controlla se un promemoria è già stato generato per oggi
                                is_already_generated = any(
                                    datetime.fromisoformat(s['datetime']).date() == today
                                    for s in colony.get('feeding_schedule', [])
                                )
                                if not is_already_generated:
                                    logger.info(f"Generando promemoria ricorrente per {colony['name']} per la data {today}")
                                    new_schedule = {
                                        "datetime": datetime.combine(today, datetime.min.time()).isoformat(),
                                        "description": f"Promemoria ricorrente (ogni {interval} giorni)",
                                        "food_type": recurring.get('food_type', ''),
                                        "quantity": recurring.get('quantity', '')
                                    }
                                    colony['feeding_schedule'].append(new_schedule)
                                    self.save_data()
                    except (ValueError, KeyError) as e:
                        logger.error(f"Errore nel formato del promemoria ricorrente per la colonia {colony['name']}: {e}")
                        colony['recurring_schedule'].remove(recurring)
                        self.save_data()

                # Gestisci i promemoria singoli
                for schedule_dict in list(colony.get("feeding_schedule", [])):
                    try:
                        schedule_dt = datetime.fromisoformat(schedule_dict['datetime'])
                        description = schedule_dict.get('description', '')
                        
                        if now >= schedule_dt and now < schedule_dt + timedelta(minutes=5):
                            logger.info(f"Promemoria singolo trovato per la colonia {colony['name']} alle {schedule_dt.strftime('%H:%M')}")
                            if self.settings.get("notifications_desktop") and NOTIFICATIONS_AVAILABLE:
                                self._send_desktop_notification(colony["name"], schedule_dt, description)
                            if self.settings.get("notifications_email"):
                                self._send_email_notification(colony["name"], schedule_dt, description)
                            
                            # Rimuovi il promemoria dalla lista, l'utente lo segnerà come completato
                            # per registrarlo nella cronologia
                            # colony["feeding_schedule"].remove(schedule_dict)
                            # self.save_data() 
                            logger.info(f"Notifica inviata per {colony['name']}")

                    except (ValueError, KeyError) as e:
                        logger.error(f"Errore nel formato del promemoria per la colonia {colony['name']}: {e}")
                        # Rimuovi il promemoria corrotto per evitare errori futuri
                        colony["feeding_schedule"].remove(schedule_dict)
                        self.save_data()
                        
            time.sleep(60)
            
    def _send_desktop_notification(self, colony_name, schedule_dt, description):
        notification_title = f"Promemoria Alimentazione - {colony_name}"
        notification_message = f"È ora di nutrire la colonia '{colony_name}'! (Alle {schedule_dt.strftime('%H:%M')})"
        if description:
            notification_message += f"\nNote: {description}"
        notification.notify(
            title=notification_title,
            message=notification_message,
            app_name="Ant Colony Monitor"
        )
        logger.debug("Notifica desktop inviata.")
    
    def _send_email_notification(self, colony_name, schedule_dt, description):
        sender_email = self.settings.get("email_sender")
        password = self.settings.get("email_password")
        recipient_email = self.settings.get("email_recipient")
        smtp_server = self.settings.get("smtp_server")
        port = self.settings.get("smtp_port")

        if not all([sender_email, password, recipient_email, smtp_server, port]):
            logger.warning("Impostazioni email incomplete. Impossibile inviare la notifica.")
            return

        subject = f"Promemoria Alimentazione: {colony_name}"
        body = (f"Ciao,\n\nQuesto è un promemoria per l'alimentazione della colonia '{colony_name}'.\n"
                f"L'orario di alimentazione è alle {schedule_dt.strftime('%H:%M')} di oggi, {schedule_dt.strftime('%d-%m-%Y')}.\n")
        if description:
            body += f"Note: {description}\n\n"
        body += f"Saluti,\nAnt Colony Monitor"

        try:
            context = ssl.create_default_context()
            if port == 465:
                with smtplib.SMTP_SSL(smtp_server, port, context=context) as server:
                    server.login(sender_email, password)
                    message = f"Subject: {subject}\n\n{body}"
                    server.sendmail(sender_email, recipient_email, message.encode('utf-8'))
            else:
                with smtplib.SMTP(smtp_server, port) as server:
                    server.starttls(context=context)
                    server.login(sender_email, password)
                    message = f"Subject: {subject}\n\n{body}"
                    server.sendmail(sender_email, recipient_email, message.encode('utf-8'))
            logger.info(f"Notifica email inviata con successo per la colonia {colony_name}.")
        except smtplib.SMTPAuthenticationError:
            logger.error("Errore di autenticazione SMTP. Controlla email e password nelle impostazioni.")
        except Exception as e:
            logger.error(f"Errore durante l'invio della notifica email per la colonia {colony_name}: {e}")

    def check_for_updates(self, silent=False):
        try:
            url = self.settings.get("update_url", DEFAULT_UPDATE_URL)
            # Use a timeout to prevent hanging
            with urllib.request.urlopen(url, timeout=5) as response:
                content = response.read().decode('utf-8')
            
            # Simple regex to find CURRENT_VERSION = "x.y.z"
            match = re.search(r'CURRENT_VERSION\s*=\s*"([^"]+)"', content)
            if match:
                remote_version = match.group(1)
                if remote_version != CURRENT_VERSION:
                    msg = f"Nuova versione {remote_version} disponibile!"
                    self.root.after(0, lambda: messagebox.showinfo("Aggiornamento", msg))
                elif not silent:
                    self.root.after(0, lambda: messagebox.showinfo("Aggiornamento", "Nessun aggiornamento disponibile."))
        except Exception as e:
            logger.error(f"Errore controllo aggiornamenti: {e}")
            if not silent:
                 self.root.after(0, lambda: messagebox.showerror("Errore", f"Impossibile controllare aggiornamenti: {e}"))

    # Nuovo metodo per la chiusura definitiva
    def close_app(self):
        self.notification_thread_running = False
        self.root.destroy()

    def __del__(self):
        self.notification_thread_running = False

def main():
    if not os.path.exists(IMAGE_DIR):
        os.makedirs(IMAGE_DIR)

    root = tk.Tk()

    try:
        icon_path = os.path.join(SCRIPT_DIR, "ant_icon.ico")
        root.iconbitmap(icon_path)
    except tk.TclError:
        pass

    app = AntColonyApp(root)

    # Funzione per creare un'icona segnaposto se il file non esiste
    def create_placeholder_image():
        size = (64, 64)
        image = Image.new('RGB', size, 'white')
        d = ImageDraw.Draw(image)
        d.rectangle((size[0]//4, size[1]//4, 3*size[0]//4, 3*size[1]//4), fill='black')
        return image

    # Modifiche per la gestione dell'icona di sistema
    if PYSTRAY_AVAILABLE:
        try:
            image_path = "ant_icon.png"
            if os.path.exists(image_path):
                image = Image.open(image_path)
            else:
                print("Avviso: 'ant_icon.png' non trovata. Verrà usata un'icona segnaposto.")
                image = create_placeholder_image()
            
            def show_window(icon, item):
                icon.stop()
                root.after(0, root.deiconify)
                root.after(0, root.lift)

            def exit_app(icon, item):
                icon.stop()
                app.close_app()
                
            menu = Menu(item('Mostra', show_window), item('Esci', exit_app))
            icon = TrayIcon('Ant Colony Monitor', image, 'Ant Colony Monitor', menu)

            def on_closing():
                root.withdraw()
                threading.Thread(target=icon.run, daemon=True).start()
            
            root.protocol("WM_DELETE_WINDOW", on_closing)

        except Exception as e:
            print(f"Errore nella configurazione di pystray: {e}")
            def on_closing():
                if messagebox.askokcancel("Chiudi", "Sei sicuro di voler chiudere l'applicazione?"):
                    app.close_app()
            root.protocol("WM_DELETE_WINDOW", on_closing)
    else:
        def on_closing():
            if messagebox.askokcancel("Chiudi", "Sei sicuro di voler chiudere l'applicazione?"):
                app.close_app()
        root.protocol("WM_DELETE_WINDOW", on_closing)

    root.mainloop()

if __name__ == "__main__":
    main()