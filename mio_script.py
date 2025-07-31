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
import math
import smtplib
import ssl
from io import BytesIO

try:
    from plyer import notification
    NOTIFICATIONS_AVAILABLE = True
except ImportError:
    NOTIFICATIONS_AVAILABLE = False
    print("Nota: Per le notifiche installa: pip install plyer")

try:
    from pystray import MenuItem as item, Menu
    from pystray import Icon as TrayIcon
    PYSTRAY_AVAILABLE = True
except ImportError:
    PYSTRAY_AVAILABLE = False
    print("Nota: Per la riduzione a icona nella barra di sistema installa: pip install pystray")

# --- Costanti ---
DATA_FILE = "colonies.json"
IMAGE_DIR = "colony_images"
BACKUP_DIR = "backups"
DEFAULT_BG_COLOR = "#1a233b"  # Blu scuro
CARD_BG_COLOR = "#212e4d"   # Blu più chiaro per i pannelli
TEXT_COLOR = "#ecf0f1"
ACCENT_COLOR = "#3498db"
GRAPH_COLOR = "#2ecc71" # Verde per il grafico

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

        self.colonies = []
        self.settings = {}
        self.colonies, self.settings = self.load_data()
        self.create_backup()

        self.current_colony = None
        self.current_calendar_date = datetime.now()
        self.last_size = (0, 0)
        self.last_colony_grid_width = 0

        # Gestione dell'immagine di sfondo
        self._current_background_label = None
        self._current_background_photo = None
        self.background_image_path = self.settings.get("background_image_path")
        self.update_background_image()
        self.root.bind("<Configure>", self.on_window_resize)

        # Avvia il thread per il controllo delle notifiche
        self.notification_thread_running = False
        self.start_notification_thread()

        self.create_main_frame()
        self.center_window()

    def load_data(self):
        colonies = []
        settings = {
            "notifications": True,
            "notifications_email": False,
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
                    settings.update(data.get("settings", {}))
                    
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
                
        return colonies, settings

    def save_data(self):
        try:
            with open(DATA_FILE, 'w', encoding='utf-8') as f:
                data = {
                    "colonies": self.colonies,
                    "settings": self.settings
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

        # Stile per la Checkbox (Toggle.TButton)
        self.style.configure("Toggle.TCheckbutton", 
                             foreground=TEXT_COLOR, background=CARD_BG_COLOR,
                             indicatorcolor=CARD_BG_COLOR,
                             indicatorbackground="#7f8c8d",
                             indicatormargin=5,
                             indicatordiameter=15)
        self.style.map("Toggle.TCheckbutton",
                       indicatorcolor=[('selected', ACCENT_COLOR)])
        
    def create_main_frame(self):
        self.clear_frame()
        self.current_colony = None # Resetta la colonia attuale

        main_container = tk.Frame(self.root, bg=DEFAULT_BG_COLOR)
        main_container.pack(fill="both", expand=True)

        self._create_main_header(main_container)

        content_frame = tk.Frame(main_container, bg=DEFAULT_BG_COLOR)
        content_frame.pack(fill="both", expand=True, padx=20, pady=20)

        if not self.colonies:
            empty_frame = tk.Frame(content_frame, bg=DEFAULT_BG_COLOR)
            empty_frame.pack(expand=True, fill="both")

            empty_label = tk.Label(empty_frame,
                                 text="🔍 Nessuna colonia registrata\n\nClicca su 'Nuova Colonia' per iniziare!",
                                 font=("Segoe UI", 16),
                                 fg="#95a5a6",
                                 bg=DEFAULT_BG_COLOR,
                                 justify="center")
            empty_label.pack(expand=True)
            return

        self.canvas = tk.Canvas(content_frame, bg=DEFAULT_BG_COLOR, highlightthickness=0)
        self.scrollbar = ttk.Scrollbar(content_frame, orient="vertical", command=self.canvas.yview)
        self.scrollable_frame = tk.Frame(self.canvas, bg=DEFAULT_BG_COLOR)

        self.scrollable_frame.bind(
            "<Configure>",
            lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all"))
        )

        self.canvas.create_window((0, 0), window=self.scrollable_frame, anchor="nw")
        self.canvas.configure(yscrollcommand=self.scrollbar.set)
        
        self.canvas.bind("<MouseWheel>", self._on_mousewheel)

        self.canvas.pack(side="left", fill="both", expand=True)
        self.scrollbar.pack(side="right", fill="y")

        self.display_colonies()
        self.update_background_image()

    def _on_mousewheel(self, event):
        self.canvas.yview_scroll(int(-1*(event.delta/120)), "units")

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

        ttk.Button(btn_frame, text="➕ Nuova Colonia",
                  style="Success.TButton",
                  command=self.create_colony).pack(side="right", padx=5)

    def display_colonies(self):
        for widget in self.scrollable_frame.winfo_children():
            widget.destroy()

        grid_frame = tk.Frame(self.scrollable_frame, bg=DEFAULT_BG_COLOR)
        grid_frame.pack(fill="both", expand=True, padx=10, pady=10)

        # Calcola il numero di colonne in base alla larghezza della finestra
        canvas_width = self.canvas.winfo_width()
        num_columns = max(1, min(3, canvas_width // 350))
        self.last_colony_grid_width = num_columns
        
        for i in range(num_columns):
            grid_frame.grid_columnconfigure(i, weight=1)

        for idx, colony in enumerate(self.colonies):
            row = idx // num_columns
            col = idx % num_columns
            
            card = tk.Frame(grid_frame, bg=CARD_BG_COLOR, relief="raised", bd=2)
            card.grid(row=row, column=col, padx=15, pady=15, sticky="nsew")

            card_content = tk.Frame(card, bg=CARD_BG_COLOR)
            card_content.pack(fill="both", expand=True, padx=20, pady=20)

            img_frame = tk.Frame(card_content, bg=CARD_BG_COLOR)
            img_frame.pack(pady=(0, 15))
            self._create_colony_image_card(img_frame, colony)

            name_label = tk.Label(card_content,
                                text=colony["name"],
                                font=("Segoe UI", 14, "bold"),
                                fg=TEXT_COLOR,
                                bg=CARD_BG_COLOR)
            name_label.pack(pady=(0, 5))

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

            # Prendi l'ultima popolazione registrata
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
                                      wraplength=200)
                desc_label.pack(pady=2)

            btn_frame = tk.Frame(card_content, bg=CARD_BG_COLOR)
            btn_frame.pack(pady=(15, 0))

            ttk.Button(btn_frame, text="Apri",
                      style="Modern.TButton",
                      command=lambda c=colony: self.show_colony(c)).pack(side="left", padx=5)

            ttk.Button(btn_frame, text="Elimina",
                      style="Danger.TButton",
                      command=lambda c=colony: self.delete_colony(c)).pack(side="left", padx=5)
    
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
                img.thumbnail((180, 180), Image.LANCZOS)
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
        dialog.geometry("400x550")
        dialog.configure(bg=CARD_BG_COLOR)
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.focus_set()

        dialog.geometry(f"+{self.root.winfo_rootx()+200}+{self.root.winfo_rooty()+150}")

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
        name_entry.pack(fill="x", pady=(0, 15))
        name_entry.focus()

        tk.Label(content, text="Descrizione (opzionale):",
                font=("Segoe UI", 12),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", pady=(0, 5))

        description_text = scrolledtext.ScrolledText(content, wrap="word", width=30, height=5,
                                                    font=("Segoe UI", 10),
                                                    bg=DEFAULT_BG_COLOR, fg=TEXT_COLOR,
                                                    insertbackground=TEXT_COLOR)
        description_text.pack(fill="x", pady=(0, 15))

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
                messagebox.showerror("Errore", "Il nome della colonia è obbligatorio!")
                return
            
            try:
                initial_pop = int(pop_var.get())
            except ValueError:
                messagebox.showerror("Errore", "La popolazione deve essere un numero intero.")
                return

            new_colony = {
                "name": name,
                "collection_date": date_entry.get(),
                "description": description,
                "notes": "",
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
        dialog.geometry("400x450")
        dialog.configure(bg=CARD_BG_COLOR)
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.focus_set()

        dialog.geometry(f"+{self.root.winfo_rootx()+200}+{self.root.winfo_rooty()+150}")

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
        name_entry.pack(fill="x", pady=(0, 15))
        name_entry.focus()

        tk.Label(content, text="Descrizione:",
                font=("Segoe UI", 12),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", pady=(0, 5))

        description_text = scrolledtext.ScrolledText(content, wrap="word", width=30, height=5,
                                                    font=("Segoe UI", 10),
                                                    bg=DEFAULT_BG_COLOR, fg=TEXT_COLOR,
                                                    insertbackground=TEXT_COLOR)
        description_text.insert(tk.END, self.current_colony.get("description", ""))
        description_text.pack(fill="x", pady=(0, 15))

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

            self.current_colony["name"] = name
            self.current_colony["description"] = description
            self.current_colony["collection_date"] = date_entry.get()
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

    def show_settings(self):
        dialog = tk.Toplevel(self.root)
        dialog.title("Impostazioni")
        dialog.geometry("550x550")
        dialog.configure(bg=CARD_BG_COLOR)
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.focus_set()

        dialog.geometry(f"+{self.root.winfo_rootx()+200}+{self.root.winfo_rooty()+150}")

        content = tk.Frame(dialog, bg=CARD_BG_COLOR)
        content.pack(fill="both", expand=True, padx=30, pady=30)

        tk.Label(content, text="⚙️ Impostazioni",
                font=("Segoe UI", 16, "bold"),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(pady=(0, 20))

        # Notifiche
        notif_frame = tk.Frame(content, bg=CARD_BG_COLOR)
        notif_frame.pack(fill="x", pady=10)
        tk.Label(notif_frame, text="Opzioni Notifiche:",
                font=("Segoe UI", 12, "bold"),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", pady=(0, 5))

        self.notif_desktop_var = tk.BooleanVar(value=self.settings.get("notifications_desktop", True))
        notif_desktop_check = ttk.Checkbutton(notif_frame, text="Notifiche desktop",
                                            variable=self.notif_desktop_var,
                                            style="Toggle.TButton")
        notif_desktop_check.pack(anchor="w", padx=5)

        self.notif_email_var = tk.BooleanVar(value=self.settings.get("notifications_email", False))
        notif_email_check = ttk.Checkbutton(notif_frame, text="Notifiche email",
                                            variable=self.notif_email_var,
                                            style="Toggle.TButton")
        notif_email_check.pack(anchor="w", padx=5)

        # Email settings
        email_frame = tk.Frame(content, bg=CARD_BG_COLOR)
        email_frame.pack(fill="x", pady=10)
        tk.Label(email_frame, text="Configurazione Email:",
                font=("Segoe UI", 12, "bold"),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", pady=(0, 5))
        
        tk.Label(email_frame, text="Email mittente:", fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w")
        self.email_sender_var = tk.StringVar(value=self.settings.get("email_sender", ""))
        email_sender_entry = tk.Entry(email_frame, textvariable=self.email_sender_var, width=40)
        email_sender_entry.pack(fill="x", padx=5, pady=2)
        
        tk.Label(email_frame, text="Password (o password per app):", fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w")
        self.email_password_var = tk.StringVar(value=self.settings.get("email_password", ""))
        email_password_entry = tk.Entry(email_frame, textvariable=self.email_password_var, width=40, show="*")
        email_password_entry.pack(fill="x", padx=5, pady=2)
        
        tk.Label(email_frame, text="Email destinatario:", fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w")
        self.email_recipient_var = tk.StringVar(value=self.settings.get("email_recipient", ""))
        email_recipient_entry = tk.Entry(email_frame, textvariable=self.email_recipient_var, width=40)
        email_recipient_entry.pack(fill="x", padx=5, pady=2)

        smtp_frame = tk.Frame(email_frame, bg=CARD_BG_COLOR)
        smtp_frame.pack(fill="x")
        
        tk.Label(smtp_frame, text="Server SMTP:", fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(side="left")
        self.smtp_server_var = tk.StringVar(value=self.settings.get("smtp_server", "smtp.gmail.com"))
        smtp_server_entry = tk.Entry(smtp_frame, textvariable=self.smtp_server_var, width=20)
        smtp_server_entry.pack(side="left", padx=5)

        tk.Label(smtp_frame, text="Porta:", fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(side="left")
        self.smtp_port_var = tk.StringVar(value=str(self.settings.get("smtp_port", 587)))
        smtp_port_entry = tk.Entry(smtp_frame, textvariable=self.smtp_port_var, width=5)
        smtp_port_entry.pack(side="left", padx=5)
        
        ttk.Button(email_frame, text="Invia Email di Prova",
                   style="Modern.TButton",
                   command=self.test_email_connection).pack(pady=5)

        # Backup settings
        backup_frame = tk.Frame(content, bg=CARD_BG_COLOR)
        backup_frame.pack(fill="x", pady=10)

        tk.Label(backup_frame, text="Gestione Backup:",
                font=("Segoe UI", 12, "bold"),
                fg=TEXT_COLOR, bg=CARD_BG_COLOR).pack(anchor="w", pady=(0, 10))

        ttk.Button(backup_frame, text="Crea Backup Ora",
                  style="Modern.TButton",
                  command=self.create_backup).pack(side="left", padx=5)

        ttk.Button(backup_frame, text="Ripristina Backup",
                  style="Warning.TButton",
                  command=self.restore_backup).pack(side="left", padx=5)
        
        btn_frame = tk.Frame(content, bg=CARD_BG_COLOR)
        btn_frame.pack(fill="x", pady=20)
        
        def save_settings():
            self.settings["notifications_email"] = self.notif_email_var.get()
            self.settings["notifications_desktop"] = self.notif_desktop_var.get()
            self.settings["email_sender"] = self.email_sender_var.get().strip()
            self.settings["email_password"] = self.email_password_var.get().strip()
            self.settings["email_recipient"] = self.email_recipient_var.get().strip()
            self.settings["smtp_server"] = self.smtp_server_var.get().strip()
            try:
                self.settings["smtp_port"] = int(self.smtp_port_var.get().strip())
            except ValueError:
                messagebox.showerror("Errore", "La porta SMTP deve essere un numero intero.")
                return

            self.save_data()
            dialog.destroy()
            messagebox.showinfo("Successo", "Impostazioni salvate con successo!")
            self.restart_notification_thread()

        ttk.Button(btn_frame, text="Salva Impostazioni",
                  style="Success.TButton",
                  command=save_settings).pack(side="right", padx=5)
        
        ttk.Button(btn_frame, text="Annulla",
                  style="Modern.TButton",
                  command=dialog.destroy).pack(side="right", padx=5)

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

    def create_backup(self):
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
            messagebox.showinfo("Backup", "Backup creato con successo!")
        except Exception as e:
            messagebox.showerror("Errore", f"Errore durante il backup: {e}")

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
                    shutil.copy(backup_file, DATA_FILE)
                    self.colonies, self.settings = self.load_data()
                    dialog.destroy()
                    self.create_main_frame()
                    messagebox.showinfo("Successo", "Backup ripristinato con successo!")
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
                    new_num_columns = max(1, min(3, self.canvas.winfo_width() // 350))
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
            self.update_background_image()

    def update_background_image(self):
        if self._current_background_label:
            self._current_background_label.destroy()
            self._current_background_label = None
            self._current_background_photo = None
        
        if self.background_image_path and os.path.exists(self.background_image_path):
            try:
                img = Image.open(self.background_image_path)
                root_width, root_height = self.root.winfo_width(), self.root.winfo_height()
                if root_width > 0 and root_height > 0:
                    img_ratio = img.width / img.height
                    root_ratio = root_width / root_height
                    if root_ratio > img_ratio:
                        new_width = root_width
                        new_height = int(root_width / img_ratio)
                    else:
                        new_height = root_height
                        new_width = int(root_height * img_ratio)
                        
                    img = img.resize((new_width, new_height), Image.LANCZOS)
                    self._current_background_photo = ImageTk.PhotoImage(img)
                    
                    self._current_background_label = tk.Label(self.root, image=self._current_background_photo)
                    self._current_background_label.place(x=0, y=0, relwidth=1, relheight=1)
                    self._current_background_label.lower()
            except Exception as e:
                print(f"Errore nel caricamento dell'immagine di sfondo: {e}")
                self.background_image_path = None
                self.settings["background_image_path"] = None
                self.save_data()
    
    def clear_frame(self):
        for widget in self.root.winfo_children():
            if widget is not self._current_background_label:
                widget.destroy()

    def show_calendar(self):
        self.clear_frame()
        self.current_colony = None # Resetta la colonia attuale

        main_container = tk.Frame(self.root, bg=DEFAULT_BG_COLOR)
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
        
        self.calendar_grid_frame = tk.Frame(parent, bg=DEFAULT_BG_COLOR)
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
                    
                    if today >= start_date:
                        days_since_start = (today - start_date).days
                        if days_since_start % interval == 0:
                            dates.add(today)
                        
                        # Aggiungi anche gli eventi futuri nel mese corrente
                        current_date = start_date
                        while current_date.month <= self.current_calendar_date.month and current_date.year <= self.current_calendar_date.year:
                            if current_date.month == self.current_calendar_date.month:
                                dates.add(current_date)
                            current_date += timedelta(days=interval)
                        
                except (KeyError, ValueError):
                    pass
        return dates

    def delete_colony(self, colony):
        if messagebox.askyesno("Elimina Colonia", f"Sei sicuro di voler eliminare la colonia '{colony['name']}'?"):
            self.colonies.remove(colony)
            self.save_data()
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
                img.thumbnail((200, 200), Image.LANCZOS)
                photo = ImageTk.PhotoImage(img)
                self.profile_img_label.config(image=photo)
                self.profile_img_label.image = photo
            except (IOError, OSError):
                self.create_placeholder_image(self.profile_img_label.master)
        else:
            self.create_placeholder_image(self.profile_img_label.master)

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
                    img.thumbnail((150, 150), Image.LANCZOS)
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
             print("Thread di notifica avviato.")
        else:
            print("Notifiche disabilitate nelle impostazioni.")

    def restart_notification_thread(self):
        self.notification_thread_running = False
        time.sleep(1)  # Dà al vecchio thread il tempo di terminare
        self.start_notification_thread()

    def _check_notifications(self):
        while self.notification_thread_running:
            now = datetime.now()
            today = now.date()
            print(f"Controllo notifiche... Ora attuale: {now.strftime('%H:%M:%S')}")
            
            for colony in self.colonies:
                # Gestisci i promemoria ricorrenti
                for recurring in list(colony.get("recurring_schedule", [])):
                    try:
                        start_date = datetime.fromisoformat(recurring['start_date']).date()
                        interval = recurring['interval']

                        if today >= start_date:
                            days_since_start = (today - start_date).days
                            if days_since_start % interval == 0:
                                # Controlla se un promemoria è già stato generato per oggi
                                is_already_generated = any(
                                    datetime.fromisoformat(s['datetime']).date() == today
                                    for s in colony.get('feeding_schedule', [])
                                )
                                if not is_already_generated:
                                    print(f"Generando promemoria ricorrente per {colony['name']} per la data {today}")
                                    new_schedule = {
                                        "datetime": datetime.combine(today, datetime.min.time()).isoformat(),
                                        "description": f"Promemoria ricorrente (ogni {interval} giorni)",
                                        "food_type": recurring.get('food_type', ''),
                                        "quantity": recurring.get('quantity', '')
                                    }
                                    colony['feeding_schedule'].append(new_schedule)
                                    self.save_data()
                    except (ValueError, KeyError) as e:
                        print(f"Errore nel formato del promemoria ricorrente per la colonia {colony['name']}: {e}")
                        colony['recurring_schedule'].remove(recurring)
                        self.save_data()

                # Gestisci i promemoria singoli
                for schedule_dict in list(colony.get("feeding_schedule", [])):
                    try:
                        schedule_dt = datetime.fromisoformat(schedule_dict['datetime'])
                        description = schedule_dict.get('description', '')
                        
                        if now >= schedule_dt and now < schedule_dt + timedelta(minutes=5):
                            print(f"Promemoria singolo trovato per la colonia {colony['name']} alle {schedule_dt.strftime('%H:%M')}")
                            if self.settings.get("notifications_desktop") and NOTIFICATIONS_AVAILABLE:
                                self._send_desktop_notification(colony["name"], schedule_dt, description)
                            if self.settings.get("notifications_email"):
                                self._send_email_notification(colony["name"], schedule_dt, description)
                            
                            # Rimuovi il promemoria dalla lista, l'utente lo segnerà come completato
                            # per registrarlo nella cronologia
                            # colony["feeding_schedule"].remove(schedule_dict)
                            # self.save_data() 
                            print(f"Notifica inviata per {colony['name']}")

                    except (ValueError, KeyError) as e:
                        print(f"Errore nel formato del promemoria per la colonia {colony['name']}: {e}")
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
        print("Notifica desktop inviata.")
    
    def _send_email_notification(self, colony_name, schedule_dt, description):
        sender_email = self.settings.get("email_sender")
        password = self.settings.get("email_password")
        recipient_email = self.settings.get("email_recipient")
        smtp_server = self.settings.get("smtp_server")
        port = self.settings.get("smtp_port")

        if not all([sender_email, password, recipient_email, smtp_server, port]):
            print("Avviso: le impostazioni email non sono complete. Impossibile inviare la notifica.")
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
            print(f"Notifica email inviata con successo per la colonia {colony_name}.")
        except smtplib.SMTPAuthenticationError:
            print("Errore di autenticazione SMTP. Controlla email e password nelle impostazioni.")
        except Exception as e:
            print(f"Errore durante l'invio della notifica email per la colonia {colony_name}: {e}")

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
        root.iconbitmap("ant_icon.ico")
    except:
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